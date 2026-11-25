-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisConv_summable_prod_tuple
-- name    : GlobalTheory.SW.EisConv.summable_prod_tuple
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:11.880341+00:00
-- url     : https://prove2.me/theorems/622bf83b-2bc9-4d44-b938-99fe0791ed3a
-- title:
--   Eis Conv: summable prod tuple
-- statement:
--   The Eis Conv construction uses the summable prod tuple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L56-L64

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

theorem GlobalTheory.SW.EisConv.summable_prod_tuple {α : Type} {g : α → ℝ} (hg : Summable g) (h0 : ∀ a, 0 ≤ g a) (N : ℕ) :
    Summable fun x : Fin N → α => ∏ i, g (x i) := by sorry
