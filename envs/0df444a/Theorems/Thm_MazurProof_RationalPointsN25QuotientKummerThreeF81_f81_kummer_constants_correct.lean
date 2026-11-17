-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81_kummer_constants_correct
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_constants_correct
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:11.560705+00:00
-- url     : https://prove2.me/theorems/76c802d3-32b9-4de0-bd2c-10a1598cd458
-- title:
--   The explicit $\mathbf F_{81}$ cyclotomic and Kummer constants
-- statement:
--   Let $\mathbf F_{81}=\mathbf F_3[q]/(q^4+2q^3+2)$ and set $e=1+2q+2q^2$, $e_2=2+q+2q^2$, $A=2+2q^3$, and $B=1+2q+q^2+q^3$. With the explicit field operations, these constants satisfy
--
--   $$e^4+e^3+e^2+e+1=0,\qquad e^2=e_2,\qquad -e^3+e+1=A,\qquad e^3-e^2-e+1=B.$$
--
--   This validates the stored constants used in the one-parameter Kummer computation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitF81Field
import Definitions.Def_N25_ExplicitKummerThree
import Definitions.Def_N25_ExplicitKummerThreeF81

open MazurProof
open MazurProof.RationalPointsN25QuotientKummerThreeF81
open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientKummerThree
open scoped BigOperators
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

theorem MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_constants_correct :
    let O := f81Operations
    let e := f81FifthRoot25
    let eSq := ternaryPow O e 2
    let eCube := ternaryPow O e 3
    let eFourth := ternaryPow O e 4
    O.add (O.add (O.add (O.add eFourth eCube) eSq) e) O.one = O.zero ∧
    eSq = f81FifthRootSq25 ∧
    O.add (O.add (O.mul (O.neg O.one) eCube) e) O.one = f81KummerA25 ∧
    O.add (O.add (O.add eCube (O.neg eSq)) (O.neg e)) O.one =
      f81KummerB25 := by sorry
