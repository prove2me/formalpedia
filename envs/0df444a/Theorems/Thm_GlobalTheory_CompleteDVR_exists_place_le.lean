-- Prove2me | Theorems.Thm_GlobalTheory_CompleteDVR_exists_place_le
-- name    : GlobalTheory.CompleteDVR.exists_place_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:41.579684+00:00
-- url     : https://prove2.me/theorems/bf26da41-0966-4b0b-b3bc-09f0b4fc84cd
-- title:
--   Complete DVR: exists place le
-- statement:
--   The Complete DVR construction uses the exists place le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteDvrExtension.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteDvrExtension.lean#L8-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing HeightOneSpectrum
open GlobalTheory GlobalTheory.CompleteDVR

theorem GlobalTheory.CompleteDVR.exists_place_le {K : Type} [Field K] [NumberField K] (W : ValuationSubring K) :
    ∃ la : HeightOneSpectrum (𝓞 K), (la.valuation K).valuationSubring ≤ W := by sorry
