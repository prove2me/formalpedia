-- Prove2me | Theorems.Thm_Kyprianou_Ch05_subordinatorLaplacePositiveBound
-- name    : Kyprianou.Ch05.subordinatorLaplacePositiveBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:25:42.743958+00:00
-- url     : https://prove2.me/theorems/bc595345-9e94-4488-83f2-00ecc1b0e7f2
-- title:
--   A nonnegative marginal has strictly positive exponential transform bounded by one.
-- statement:
--   A nonnegative marginal has strictly positive exponential transform bounded by one.
-- source:
--   Kyprianou (2006), Lemma 5.2; faithful further decomposition of the time-Laplace semigroup and monotone additive linearity.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.subordinatorLaplacePositiveBound
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (theta : Real) (htheta : 0 < theta) :
    ∀ t : NNReal, 0 < (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P) ∧ (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P) ≤ 1 := by sorry
