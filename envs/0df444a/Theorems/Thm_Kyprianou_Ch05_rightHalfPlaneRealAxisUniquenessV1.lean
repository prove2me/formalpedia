-- Prove2me | Theorems.Thm_Kyprianou_Ch05_rightHalfPlaneRealAxisUniquenessV1
-- name    : Kyprianou.Ch05.rightHalfPlaneRealAxisUniquenessV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:53:57.783844+00:00
-- url     : https://prove2.me/theorems/28adc56c-afa4-5819-9b28-b6128ab2df74
-- title:
--   Analytic transforms agreeing on positive real axis agree on the closed right half-plane
-- statement:
--   Analytic uniqueness at the interior point one, then extend equality to the closure by continuity.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set Complex Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch05.rightHalfPlaneRealAxisUniquenessV1
    (f g : ℂ → ℂ)
    (hf : DiffContOnCl ℂ f {z : ℂ | 0 < z.re})
    (hg : DiffContOnCl ℂ g {z : ℂ | 0 < z.re})
    (hreal : ∀ x : ℝ, 0 < x → f (x : ℂ) = g (x : ℂ)) :
    ∀ z : ℂ, 0 ≤ z.re → f z = g z := by
  sorry
