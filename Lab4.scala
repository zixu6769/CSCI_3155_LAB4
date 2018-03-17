package jsy.student

import jsy.lab4.Lab4Like

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser

  /*
   * CSCI 3155: Lab 4
   * <Your Name>
   *
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /* Collections and Higher-Order Functions */

  /* Lists */

  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => {
      if (h1 == h2) compressRec(t1)
      else h1 :: compressRec(t1)
    }
  }

  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match{
      case Nil => h :: Nil
      case h2 :: h1 => {
        if (h == h2) acc
        else h :: acc
      }
    }
  }

  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => l
    case h :: t => f(h) match {
      case None => h :: mapFirst(t){f}
      case Some(x) => x :: t
    }
  }

  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc
      case Node(l, d, r) => loop(f(loop(acc, l), d), r)
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }

  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = foldLeft(t)((true, None: Option[Int])){
      (acc,y)  => acc match {
        case (b1, None) => (b1, Some(y))
        case (b1, Some(x)) => if (x < y) (b1 && true, Some(x)) else (false, Some(x))
      }
    }
    b
  }

  /* Type Inference */

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if fields exists { case (_, t) => hasFunctionTyp(t) } => true
    case _ => false
  }

  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      //TypeVar
      case Var(x) => env(x)

      //TypeNeg
      case Unary(Neg, e1) => typeof(env, e1) match{
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }

      //TypeNot
      case Unary(Not, e1) => typeof(env, e1) match{
        case TBool => TBool
        case tgot => err(tgot, e1)
      }

      //TypeSeq
      case Binary(Seq, e1, e2) => typeof(env, e2)

      //TypeArith and TypePlusString
      case Binary(Plus, e1, e2) => (typeof(env, e1), typeof(env, e2)) match{
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case _ => err(typeof(env, e1), e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case _ => err(typeof(env, e1), e2)
      }

      //TypeInequalityNumber and TypeInequalityString
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case _ => err(typeof(env, e1), e1)
      }

      //TypeEquality
      case Binary(Eq|Ne, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (tgot1, tgot2) => if (tgot1 == tgot2 && !hasFunctionTyp(tgot1)) TBool else err(tgot1, e1)
      }

      //TypeAndOr
      case Binary(And|Or, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TBool,TBool) => TBool
        case _ => err(typeof(env, e1), e1)
      }

      //TypePrint
      case Print(e1) => typeof(env, e1); TUndefined

      //TypeIf
      case If(e1, e2, e3) => (typeof(env, e1), typeof(env, e2), typeof(env, e3)) match {
        case (TBool, a, b) => if (a == b) a else err(b, e3)
        case (c,_,_) => err(c, e1)
      }

      //TypeDecl
      case Decl(mode, x, e1, e2) => typeof(extend(env, x, typeof(env, e1)), e2)

      //TypeCall
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if params.length == args.length =>
          (params zip args).foreach {
            case ((string, mtyp), a) => if (mtyp.t != typeof(env, a)) err(typeof(env, a), a)
          }
          tret
        case tgot => err(tgot, e1)
      }

      //TypeObject
      case Obj(fields) => TObj(fields.map{ case (s,e) => (s,typeof(env, e))})

      //TypeGetField
      case GetField(e1, f) =>
        typeof(env, e1) match {
          case TObj(tfields) => tfields(f)
          case x => err(x, e1)
        }

      //TypeNumber
      case N(_) => TNumber

      //TypeBool
      case B(_) => TBool

      //TypeUndefined
      case Undefined => TUndefined

      //TypeString
      case S(_) => TString

      //TypeFunction TypeFunctionAnn TypeRecFunction
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          /***** Add cases here *****/
          case (None, _) => env
          case (Some(p1), Some(t)) => extend(env, p1, TFunction(params, t))
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = {
          params.foldLeft(env1) {
            case (acc, (s, MTyp(_, t))) => acc + (s -> t)
          }}
        // Infer the type of the function body
        val t1 = typeof(env2, e1)
        // Check with the possibly annotated return type
        tann match {
          case None => TFunction(params, t1)
          case Some(t) => if (t1 == t) TFunction(params, t1) else err(TFunction(params, t1), e1)
        }
      }
    }
  }


  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => (bop: @unchecked) match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case (N(n1), N(n2)) => (bop: @unchecked) match {
        case Lt => n1 < n2
        case Le => n1 <= n2
        case Gt => n1 > n2
        case Ge => n1 >= n2
      }
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case None => e
      case Some(ex) => loop(ex, n + 1)
    }
    loop(e0, 0)
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, esub, x))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, substitute(e1,esub,x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1,esub,x), substitute(e2,esub,x))
      case If(e1, e2, e3) => If(substitute(e1,esub,x), substitute(e2,esub,x), substitute(e3,esub,x))
      case Var(y) => if (y != x) e else esub
      case Decl(mode, y, e1, e2) => {
        if (y == x) {
          Decl(mode, y,substitute(e1,esub,x),e2)
        } else {
          Decl(mode, y,substitute(e1,esub,x), substitute(e2,esub,x))
        }
      }
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) => (p: @unchecked) match {
        case Some(y) => if (y == x || params.exists{ case (k,_) => k == x }) e else Function(Some(y), params, tann, substitute(e1, esub, x))
      }
      case Call(e1, args) => Call(substitute(e1, esub, x), args map {arg => substitute(arg, esub, x)})

      /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.mapValues(v => subst(v)))
      case GetField(e1, f) => if (x != f) GetField(subst(e1), f) else e
    }

    val fvs = freeVars(e)
    def fresh(x: String): String = if (fvs.contains(x)) fresh(x + "$") else x
    subst(rename(e)(fresh))
  }

  /* Rename bound variables in e */
  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))

        case Unary(uop, e1) => Unary(uop, ren(env, e1))
        case Binary(bop, e1, e2) => Binary(bop, ren(env, e1), ren(env, e2))
        case If(e1, e2, e3) => If(ren(env, e1), ren(env, e2), ren(env, e3))

        case Var(y) => env.get(y) match{
          case None => Var(y)
          case Some(x) => Var(x)
        }
        case Decl(mode, y, e1, e2) =>
          val yp = fresh(y)
          Decl(mode, yp, ren(env, e1), ren(env+(y->yp), e2))

        case Function(p, params, retty, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => (None, env)
            case Some(x) => {
              val pp = fresh(x)
              (Some(pp), extend(env, x, pp))
            }
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            case ((s, mt), (l: List[(String, MTyp)], e: Map[String, String])) =>
              val pp = fresh(s)
              ((pp, mt)::l, extend(e, s, pp ))
          }
          Function(pp, paramsp, retty, ren(envpp, e1))
        }

        case Call(e1, args) => Call(ren(env, e1), args map { case e => ren(env, e) })

        case Obj(fields) => Obj(fields map { case (s, e) => (fresh(s), ren(env, e))})
        case GetField(e1, f) => GetField(ren(env, e1), fresh(f))
      }
    }
    ren(empty, e)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => !isValue(e)
    case MName => false
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
        /***** Cases needing adapting from Lab 3.*/
      //DoNeg
      case Unary(Neg, v1) if isValue(v1) => v1 match{
        case N(n1) => N(-n1)
      }

      //DoNot
      case Unary(Not, v) if isValue(v) => v match{
        case B(n1) => B(!n1)
      }

      //DoSeq
      case Binary(Seq, v1, e2) if isValue(v1) => e2

      ///DoArith and DoPlusString
      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (_,S(str2)) => S(v1 + str2)
        case (S(str1),_) => S(str1 + v2)
        case (N(n1),N(n2)) => N(n1 + n2)
      }
      case Binary(Minus, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match{
        case (N(n1),N(n2)) => N(n1 - n2)
      }
      case Binary(Times, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match{
        case (N(n1),N(n2)) => N(n1 * n2)
      }
      case Binary(Div, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (N(n1), N(n2)) => N(n1 / n2)
      }

      //DoIneuqalityNumber and DoInequalityString
      case Binary(Lt, v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(Lt, v1, v2))
      case Binary(Le, v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(Le, v1, v2))
      case Binary(Gt, v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(Gt, v1, v2))
      case Binary(Ge, v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(Ge, v1, v2))

      //DoEquality
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)

      //DoAnd
      case Binary(And, v1, e2) if isValue(v1) => v1 match{
        case B(b1) => if (b1) e2 else v1
      }

      //DoOr
      case Binary(Or, v1, e2) if isValue(v1) => v1 match{
        case B(b1) => if (b1) v1 else e2
      }

      //DoIf
      case If(v1, v2, v3) if isValue(v1) => v1 match{
        case B(b1) => if (b1) v2 else v3
      }

      //DoDecl
      case Decl(mode, x, v1, e1) if isValue(v1) => substitute(e1, v1, x)

      /***** More cases here */
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (pazip.forall { case ((_, MTyp(m,_)), arg) => !isRedex(m, arg) }) {
              val e1p = pazip.foldRight(e1) {
                case (((s, _), arg), e) => substitute(e, arg, s)
              }
              p match {
                case None => e1p
                case Some(x1) => val tmp = substitute(e1p, v1, x1)
                  tmp
              }
            }
            else {
              val pazipp = mapFirst(pazip) {
                case ((k, MTyp(m, t)), arg) => if (isRedex(m, arg)) Some(((k, MTyp(m,t)), step(arg))) else None
              }
              Call(v1, pazipp map { case (_, arg) => arg } )
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. */

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. */
      //SearchUnary
      case Unary(uop, e1) => Unary(uop, step(e1))

      //SearchBinary1
      case Binary(bop, e1, e2) if !isValue(e1) => Binary(bop, step(e1), e2)

      //SearchBinary2
      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))

      //SearchIf
      case If(e1, e2, e3) if !isValue(e1) => If(step(e1), e2, e3)

      //SearchDecl
      case Decl(mode, x, e1, e2) => if(!isRedex(mode, e1)) substitute(e2, e1, x) else Decl(mode, x, step(e1), e2)

      //SearchCall1
      case Call(v1 @ Function(_, _, _, _), args) => ???

      //SearchCall2
      case Call(e1, args) => Call(step(e1), args)

        /***** New cases for Lab 4. */
      //SearchGetField
      case GetField(e1, f) => (e1: @unchecked) match {


        case Obj(fields) => (fields.get(f): @unchecked) match {
          case Some(exp) => if (isValue(exp)) exp else
            (fields.find{ case (_, v) => !isValue(v) }: @unchecked) match {
              case Some((k, v)) => Obj(fields.map{ case (k1, v1) => if (k == k1 && v == v1) (k, step(v)) else (k1,v1)} )
            }
        }
      }

      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}

