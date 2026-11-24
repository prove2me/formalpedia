-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarLevel_relIndex_perSub
-- name    : GlobalTheory.SW.HaarLevel.relIndex_perSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:58.796942+00:00
-- url     : https://prove2.me/theorems/b2a51c8f-16b5-49d6-90fd-925c7781304b
-- title:
--   Haar Level: rel Index per Sub
-- statement:
--   The Haar Level construction uses the rel Index per Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L86-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L86-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.HaarLevel.relIndex_perSub (R S : ℕ) (hR : 0 < R) :
    (perSub K κ ι (R * S)).relIndex (perSub K κ ι R) =
      S ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by sorry
