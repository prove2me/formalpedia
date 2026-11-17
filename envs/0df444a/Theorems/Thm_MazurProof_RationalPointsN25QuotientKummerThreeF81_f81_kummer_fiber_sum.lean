-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81_kummer_fiber_sum
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_fiber_sum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:57.303842+00:00
-- url     : https://prove2.me/theorems/4e64fbf2-19a8-4b8e-86dc-7dff3139d0a1
-- title:
--   The Kummer fiber sizes sum to eighty-seven
-- statement:
--   Let $s(t)$ be the certified Kummer fiber-size function on $\mathbf F_{81}$. Then the sum of all fiber sizes is
--
--   $$\sum_{t\in\mathbf F_{81}}s(t)=87.$$
--
--   This gives the total number of denominator-cleared affine Kummer solutions.
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

theorem MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_fiber_sum :
    ∑ t : F81, f81KummerFiberSize25 t = 87 := by sorry
