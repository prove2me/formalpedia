-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EntrywiseCount_card_ge
-- name    : GlobalTheory.CompanionTheory.EntrywiseCount.card_ge
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:46.771318+00:00
-- url     : https://prove2.me/theorems/c8a4f3ef-215c-4f3a-a4a7-c4d0662227d9
-- title:
--   Entrywise Count: card ge
-- statement:
--   The Entrywise Count construction uses the card ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdEntrywiseLe.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdEntrywiseLe.lean#L20-L26

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdEntrywiseLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EntrywiseCount

theorem GlobalTheory.CompanionTheory.EntrywiseCount.card_ge (n r : ℕ) (hr : r ≤ n) :
    (univ.filter (fun j : Fin n => r ≤ (j : ℕ))).card = n - r := by sorry
