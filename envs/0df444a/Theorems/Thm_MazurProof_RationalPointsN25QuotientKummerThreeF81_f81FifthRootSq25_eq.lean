-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81FifthRootSq25_eq
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeF81.f81FifthRootSq25_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:43.754204+00:00
-- url     : https://prove2.me/theorems/c5baf516-aee8-4028-9daa-96448b2f53ac
-- title:
--   The stored square of the fifth root is correct
-- statement:
--   In $\mathbf F_{81}=\mathbf F_3[q]/(q^4+2q^3+2)$, let $e=1+2q+2q^2$ and let $e_2=2+q+2q^2$ be the stored square constant. Then
--
--   $$e^2=e_2.$$
--
--   This identifies the explicit coefficient used in the Kummer numerator with the actual square of the cyclotomic eigenvalue.
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

theorem MazurProof.RationalPointsN25QuotientKummerThreeF81.f81FifthRootSq25_eq :
    f81FifthRoot25 ^ 2 = f81FifthRootSq25 := by sorry
