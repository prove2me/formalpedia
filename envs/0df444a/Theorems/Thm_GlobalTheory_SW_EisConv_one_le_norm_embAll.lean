-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisConv_one_le_norm_embAll
-- name    : GlobalTheory.SW.EisConv.one_le_norm_embAll
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:27:04.822843+00:00
-- url     : https://prove2.me/theorems/b69291e5-d51b-4629-b00a-bb655e44d543
-- title:
--   Eis Conv: one le norm emb All
-- statement:
--   The Eis Conv construction uses the one le norm emb All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L22-L27

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

theorem GlobalTheory.SW.EisConv.one_le_norm_embAll {E m : Type} [Field E] [NumberField E] [Fintype m] {w : m → 𝓞 E}
    (hw : w ≠ 0) : 1 ≤ ‖embAll E m w‖ := by sorry
