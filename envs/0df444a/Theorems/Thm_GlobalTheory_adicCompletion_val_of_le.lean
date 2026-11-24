-- Prove2me | Theorems.Thm_GlobalTheory_adicCompletion_val_of_le
-- name    : GlobalTheory.adicCompletion_val_of_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:53.848705+00:00
-- url     : https://prove2.me/theorems/c0602c81-1a10-4e87-98b3-ed50c8b3f248
-- title:
--   Global Theory: adic Completion val of le
-- statement:
--   The Global Theory construction uses the adic Completion val of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsInjectiveAdicCompletionMapOfFinite.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsInjectiveAdicCompletionMapOfFinite.lean#L13-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsInjectiveAdicCompletionMapOfFinite
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

theorem GlobalTheory.adicCompletion_val_of_le {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {m n : ℕ} (hmn : m ≤ n) (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    x.val m = Submodule.Quotient.mk d := by sorry
