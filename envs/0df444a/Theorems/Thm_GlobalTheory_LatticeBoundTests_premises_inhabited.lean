-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBoundTests_premises_inhabited
-- name    : GlobalTheory.LatticeBoundTests.premises_inhabited
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:58.061498+00:00
-- url     : https://prove2.me/theorems/7b3126b9-11e7-5573-8eee-05adb8b9a744
-- title:
--   Lattice Bound Tests: premises inhabited
-- statement:
--   The Lattice Bound Tests construction uses the premises inhabited property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/PremisesInhabited.lean#L114-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/PremisesInhabited.lean#L114-L133

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

theorem GlobalTheory.LatticeBoundTests.premises_inhabited :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (cj : E → E) (w : 𝓞 E) (Y : Type)
      (_ : AddCommGroup Y) (_ : Module (𝓞 E) Y) (_ : Module.Free ℤ Y) (_ : Module.Finite ℤ Y)
      (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ),
      (∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) ∧ (∃ z, cj z ≠ z) ∧
      (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) ∧ (w : E) + cj w = 1 ∧
      0 < Module.finrank ℤ Y ∧ (∀ x y, β x y = β y x) ∧
      (∀ c c' : 𝓞 E, (c' : E) = cj c → ∀ x y, β (c • x) y = β x (c' • y)) ∧
      ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
        (Matrix.of fun i j => β (b i) (b j)).PosDef := by sorry
