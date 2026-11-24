-- Prove2me | Theorems.Thm_GlobalTheory_exists_integral_model_of_forms
-- name    : GlobalTheory.exists_integral_model_of_forms
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:31.710109+00:00
-- url     : https://prove2.me/theorems/085b48fd-390c-42f1-8c10-91541e90b096
-- title:
--   Global Theory: exists integral model of forms
-- statement:
--   The Global Theory construction uses the exists integral model of forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIntegralModelOfForms.lean#L77-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIntegralModelOfForms.lean#L77-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve Polynomial
variable (A : Type*) [CommRing A] {K : Type*} [Field K] [Algebra A K] [IsIntegrallyClosedIn A K]
variable [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]

theorem GlobalTheory.exists_integral_model_of_forms (hj : W.j ∈ (algebraMap A K).range) (hΔ : W.Δ = 1)
    {C₂ C₃ : VariableChange K} (hu₂ : C₂.u = 1) (hu₃ : C₃.u = 1) {P Q a b : K}
    (e₂ : C₂ • W = splitCurve P Q) (e₃ : C₃ • W = deuringCurve a b) :
    ∃ (C : VariableChange K) (W₀ : WeierstrassCurve A), C • W = W₀.baseChange K ∧ W₀.Δ = 1 := by sorry
