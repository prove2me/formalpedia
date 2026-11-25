-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_pointwiseNorm_comp_flatten_symm_eq
-- name    : GlobalTheory.TensorLat.pointwiseNorm_comp_flatten_symm_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:29.082449+00:00
-- url     : https://prove2.me/theorems/e8fc5d6b-bf2d-4d49-b692-7ee4d0284c42
-- title:
--   Tensor Lat: pointwise Norm comp flatten symm eq
-- statement:
--   The Tensor Lat construction uses the pointwise Norm comp flatten symm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsBasisSpanEqOfCommensurable.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsBasisSpanEqOfCommensurable.lean#L109-L112

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

theorem GlobalTheory.TensorLat.pointwiseNorm_comp_flatten_symm_eq (X : PT E) (Y : GT (Fin n × Idx X.dim)) (q : ℕ)
    (F : (Fin n → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim) :
    Y.ptN2 q (F ∘ flat.symm) (flat v) = X.ptN2 q F v := by sorry
