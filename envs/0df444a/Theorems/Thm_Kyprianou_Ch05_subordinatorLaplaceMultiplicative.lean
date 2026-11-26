-- Prove2me | Theorems.Thm_Kyprianou_Ch05_subordinatorLaplaceMultiplicative
-- name    : Kyprianou.Ch05.subordinatorLaplaceMultiplicative
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T17:25:39.960317+00:00
-- url     : https://prove2.me/theorems/1e94a91b-44ed-4fae-b4c8-4ec3477f5436
-- title:
--   Stationary independent increments give multiplicativity of the Laplace transform.
-- statement:
--   Stationary independent increments give multiplicativity of the Laplace transform.
-- source:
--   Kyprianou (2006), Lemma 5.2; faithful further decomposition of the time-Laplace semigroup and monotone additive linearity.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.subordinatorLaplaceMultiplicative
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (theta : Real) (htheta : 0 < theta) :
    ∀ s t : NNReal, (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y (s+t) w)) ∂P) =
      (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y s w)) ∂P) * (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P) := by sorry
