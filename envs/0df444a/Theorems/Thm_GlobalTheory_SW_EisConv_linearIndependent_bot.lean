-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisConv_linearIndependent_bot
-- name    : GlobalTheory.SW.EisConv.linearIndependent_bot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:03.118174+00:00
-- url     : https://prove2.me/theorems/55586aef-5df6-4279-94e8-695bcbb45b93
-- title:
--   Eis Conv: linear Independent bot
-- statement:
--   The Eis Conv construction uses the linear Independent bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L68-L72

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

theorem GlobalTheory.SW.EisConv.linearIndependent_bot {γ : M2 E N} (h : γ ∈ UU E N) :
    LinearIndependent E fun i => γ.submatrix Sum.inr id i := by sorry
