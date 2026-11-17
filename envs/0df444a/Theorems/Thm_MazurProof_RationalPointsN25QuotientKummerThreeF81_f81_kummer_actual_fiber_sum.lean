-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81_kummer_actual_fiber_sum
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_actual_fiber_sum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:21.967203+00:00
-- url     : https://prove2.me/theorems/bfeb3fe9-eac6-4a24-a512-9e5ef614079d
-- title:
--   There are eighty-seven denominator-cleared Kummer pairs
-- statement:
--   Let $e\in\mathbf F_{81}$ be the chosen fifth-cyclotomic element, with $D_e(t)=1+A(e)t$ and $N_e(t)=t^2(B(e)+e^2t)$. Summing the actual root counts over all parameters gives
--
--   $$\sum_{t\in\mathbf F_{81}}|\{r\in\mathbf F_{81}:r^5D_e(t)+N_e(t)=0\}|=87.$$
--
--   This identifies the computed fiber sum with the cardinality of the actual Kummer solution set.
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

theorem MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_actual_fiber_sum :
    ∑ t : F81,
      Nat.card {r : F81 //
        r ^ 5 * canonicalKummerDenominator25Three f81FifthRoot25 t +
          canonicalKummerNumerator25Three f81FifthRoot25 t = 0} = 87 := by sorry
