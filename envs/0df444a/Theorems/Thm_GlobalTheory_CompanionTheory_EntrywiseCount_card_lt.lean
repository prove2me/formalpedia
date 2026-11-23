-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EntrywiseCount_card_lt
-- name    : GlobalTheory.CompanionTheory.EntrywiseCount.card_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:46.434352+00:00
-- url     : https://prove2.me/theorems/4c3071cc-4d48-4e3a-9a3b-d7ab87aeea8a
-- title:
--   Entrywise Count: card lt
-- statement:
--   The Entrywise Count construction uses the card lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdEntrywiseLe.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdEntrywiseLe.lean#L7-L18

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

theorem GlobalTheory.CompanionTheory.EntrywiseCount.card_lt (n r : ℕ) (hr : r ≤ n) :
    (univ.filter (fun i : Fin n => (i : ℕ) < r)).card = r := by sorry
