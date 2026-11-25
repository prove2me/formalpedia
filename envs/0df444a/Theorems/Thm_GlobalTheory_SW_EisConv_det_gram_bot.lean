-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisConv_det_gram_bot
-- name    : GlobalTheory.SW.EisConv.det_gram_bot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:08.767955+00:00
-- url     : https://prove2.me/theorems/bf53c35d-b95c-4f6a-aecf-66a4ae1f260a
-- title:
--   Eis Conv: det gram bot
-- statement:
--   The Eis Conv construction uses the det gram bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L74-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L74-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem GlobalTheory.SW.EisConv.det_gram_bot {γ : M2 E N} (h : γ ∈ UU E N) (τ : E →+* ℂ) :
    ((γ.submatrix Sum.inr id).map τ * ((γ.submatrix Sum.inr id).map τ)ᴴ).det.re =
      ‖(γ.toBlocks₂₁.map τ * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + γ.toBlocks₂₂.map τ).det‖ ^ 2 := by sorry
