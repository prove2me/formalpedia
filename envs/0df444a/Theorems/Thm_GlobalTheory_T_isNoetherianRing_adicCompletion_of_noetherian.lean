-- Prove2me | Theorems.Thm_GlobalTheory_T_isNoetherianRing_adicCompletion_of_noetherian
-- name    : GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:08.728594+00:00
-- url     : https://prove2.me/theorems/99c3963b-48a5-4ef3-b3e7-edf5dc35f846
-- title:
--   T: is Noetherian Ring adic Completion of noetherian
-- statement:
--   The T construction uses the is Noetherian Ring adic Completion of noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsNoetherianRingAdicCompletionOfNoetherianStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsNoetherianRingAdicCompletionOfNoetherianStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherianStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsNoetherianRing (AdicCompletion I R) := by sorry
