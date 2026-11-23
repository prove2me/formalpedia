-- Prove2me | Theorems.Thm_GlobalTheory_exists_pos_integral_comp_equiv_haar
-- name    : GlobalTheory.exists_pos_integral_comp_equiv_haar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:35.995635+00:00
-- url     : https://prove2.me/theorems/c43e4b49-dcc9-488a-867f-a5db6ba01b4b
-- title:
--   Global Theory: exists pos integral comp equiv haar
-- statement:
--   The Global Theory construction uses the exists pos integral comp equiv haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FourierInversionHaarSymmForm.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FourierInversionHaarSymmForm.lean#L8-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FourierInversionHaarSymmForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory FourierTransform
open GlobalTheory
open MeasureTheory FourierTransform

theorem GlobalTheory.exists_pos_integral_comp_equiv_haar {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : V ≃L[ℝ] E) (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∃ a : ℝ, 0 < a ∧ (∀ g : E → ℂ, ∫ x, g (T x) ∂μ = (a : ℂ) * ∫ w, g w) ∧
      ∀ g : E → ℂ, Integrable (fun x => g (T x)) μ ↔ Integrable g := by sorry
