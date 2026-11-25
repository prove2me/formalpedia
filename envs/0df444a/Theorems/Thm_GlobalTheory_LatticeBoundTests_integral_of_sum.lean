-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBoundTests_integral_of_sum
-- name    : GlobalTheory.LatticeBoundTests.integral_of_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:50.788036+00:00
-- url     : https://prove2.me/theorems/38a23e08-d496-50d8-a6da-db58e6166816
-- title:
--   Lattice Bound Tests: integral of sum
-- statement:
--   The Lattice Bound Tests construction uses the integral of sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/PremisesInhabited.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/PremisesInhabited.lean#L8-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_PremisesInhabited
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBoundTests
open NumberField

theorem GlobalTheory.LatticeBoundTests.integral_of_sum (Y : Type) [AddCommGroup Y] (S : Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ))
    (l : S →ₗ[ℝ] ℝ) (m : ℕ) (x x' : Fin m → Y)
    (h : ∀ β : S, l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i)) (β : S)
    (hβ : ∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) : ∃ z : ℤ, l β = z := by sorry
