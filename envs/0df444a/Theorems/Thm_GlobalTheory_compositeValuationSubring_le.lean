-- Prove2me | Theorems.Thm_GlobalTheory_compositeValuationSubring_le
-- name    : GlobalTheory.compositeValuationSubring_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:26.414029+00:00
-- url     : https://prove2.me/theorems/4cbf4546-5961-4e92-b727-e23fe7700bed
-- title:
--   Global Theory: composite Valuation Subring le
-- statement:
--   The Global Theory construction uses the composite Valuation Subring le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsValuationSubringLeDominatingOfFractionFiel.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsValuationSubringLeDominatingOfFractionFiel.lean#L52-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringLeDominatingOfFractionFiel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.compositeValuationSubring_le {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) : compositeValuationSubring W V ≤ W := by sorry
