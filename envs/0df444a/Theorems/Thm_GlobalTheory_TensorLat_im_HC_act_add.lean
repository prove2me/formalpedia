-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_im_HC_act_add
-- name    : GlobalTheory.TensorLat.im_HC_act_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:01.799369+00:00
-- url     : https://prove2.me/theorems/1f0606ef-184d-45db-a094-b6c6873e769c
-- title:
--   Tensor Lat: im HC act add
-- statement:
--   The Tensor Lat construction uses the im HC act add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsBasisSpanEqOfCommensurable.lean#L214-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsBasisSpanEqOfCommensurable.lean#L214-L238

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable [IsCMField E]

theorem GlobalTheory.TensorLat.im_HC_act_add (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1) (γ δ : Fin n → Vsp dim) :
    (HC (γ + δ) fun k => act w₀ ((γ + δ) k)).im =
      (HC γ fun k => act w₀ (γ k)).im + (HC δ fun k => act w₀ (δ k)).im +
        (2 * (HC γ fun k => act w₀ (δ k)).im - (HC γ δ).im) := by sorry
