-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SegOrder_exists_last_start
-- name    : GlobalTheory.CompanionTheory.SegOrder.exists_last_start
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:12:13.931971+00:00
-- url     : https://prove2.me/theorems/fc52b662-0fb9-4b31-b945-2f47a6d4bc94
-- title:
--   Seg Order: exists last start
-- statement:
--   The Seg Order construction uses the exists last start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOrderedForm.lean#L12-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOrderedForm.lean#L12-L42

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOrderedForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Zc.Comb
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SegOrder
variable {T : Type u}

theorem GlobalTheory.CompanionTheory.SegOrder.exists_last_start (s : T → T) (hs : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t)
    (m : Multiset (ASeg T)) (hm : m ≠ 0) :
    ∃ a ∈ m, ∀ b ∈ m, ¬ ∃ j : ℕ, 0 < j ∧ b.start = s^[j] a.start := by sorry
