-- Prove2me | Theorems.Thm_GlobalTheory_RegularCompletion_isRegularLocalRing_adicCompletion
-- name    : GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:17.877988+00:00
-- url     : https://prove2.me/theorems/6fc1b8f4-866d-4153-87d1-e1466876225a
-- title:
--   Regular Completion: is Regular Local Ring adic Completion
-- statement:
--   The Regular Completion construction uses the is Regular Local Ring adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsRegularLocalRingAdicCompletion.lean#L9-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsRegularLocalRingAdicCompletion.lean#L9-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.RegularCompletion

theorem GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion :
    ∀ (T : Type) [CommRing T] [IsRegularLocalRing T],
      IsRegularLocalRing (AdicCompletion (maximalIdeal T) T) := by sorry
