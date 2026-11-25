-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_polyDeriv_comp_flat_symm
-- name    : GlobalTheory.TensorLat.polyDeriv_comp_flat_symm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:28:39.317461+00:00
-- url     : https://prove2.me/theorems/d3560011-958f-437a-aaf8-ecacb6516049
-- title:
--   Tensor Lat: poly Deriv comp flat symm
-- statement:
--   The Tensor Lat construction uses the poly Deriv comp flat symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsBasisSpanEqOfCommensurable.lean#L86-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsBasisSpanEqOfCommensurable.lean#L86-L107

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
open Classical

theorem GlobalTheory.TensorLat.polyDeriv_comp_flat_symm (P : MvPolynomial (Letter n dim) ℂ)
    (F : (Fin n → Vsp dim) → ℂ) (v : Fin n → Vsp dim) :
    polyDeriv P (fun l => EuclideanSpace.single l 1) (F ∘ flat.symm) (flat v) =
      polyDeriv P dir F v := by sorry
