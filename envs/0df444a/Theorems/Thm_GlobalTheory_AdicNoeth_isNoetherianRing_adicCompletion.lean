-- Prove2me | Theorems.Thm_GlobalTheory_AdicNoeth_isNoetherianRing_adicCompletion
-- name    : GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:48.676566+00:00
-- url     : https://prove2.me/theorems/c373953a-10ad-47ff-83d4-18fccf2dbca2
-- title:
--   Adic Noeth: is Noetherian Ring adic Completion
-- statement:
--   The Adic Noeth construction uses the is Noetherian Ring adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsNoetherianRingAdicCompletionOfNoetherian.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsNoetherianRingAdicCompletionOfNoetherian.lean#L8-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsNoetherianRingOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.AdicNoeth

theorem GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsNoetherianRing (AdicCompletion I R) := by sorry
