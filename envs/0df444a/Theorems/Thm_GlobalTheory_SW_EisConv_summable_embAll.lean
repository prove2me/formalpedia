-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisConv_summable_embAll
-- name    : GlobalTheory.SW.EisConv.summable_embAll
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:52.572483+00:00
-- url     : https://prove2.me/theorems/772dba00-4f01-420d-9649-c7fdc67101e2
-- title:
--   Eis Conv: summable emb All
-- statement:
--   The Eis Conv construction uses the summable emb All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L29-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L29-L54

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

theorem GlobalTheory.SW.EisConv.summable_embAll (E m : Type) [Field E] [NumberField E] [Fintype m] (k : ℕ)
    (hk : Fintype.card m * Module.finrank ℚ E < k) :
    Summable fun w : m → 𝓞 E => ‖embAll E m w‖⁻¹ ^ k := by sorry
