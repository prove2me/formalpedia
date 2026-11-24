-- Prove2me | Theorems.Thm_GlobalTheory_SW_SiegelSum_exists_bound
-- name    : GlobalTheory.SW.SiegelSum.exists_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:44:15.913421+00:00
-- url     : https://prove2.me/theorems/87ee02ea-0b97-48c9-9dde-fa638a1204e1
-- title:
--   Siegel Sum: exists bound
-- statement:
--   The Siegel Sum construction uses the exists bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableNormSiegelThetaSeriesTerms.lean#L67-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableNormSiegelThetaSeriesTerms.lean#L67-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableProdPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SiegelSum

theorem GlobalTheory.SW.SiegelSum.exists_bound {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (hR : 0 < R)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) : ∃ M, ∀ x, ‖φ x‖ ≤ M := by sorry
