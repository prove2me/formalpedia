-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SegOrder_exists_ordered_form
-- name    : GlobalTheory.CompanionTheory.SegOrder.exists_ordered_form
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:12:20.322071+00:00
-- url     : https://prove2.me/theorems/e707be8d-19d3-43b0-9af4-e65eeb53221a
-- title:
--   Seg Order: exists ordered form
-- statement:
--   The Seg Order construction uses the exists ordered form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOrderedForm.lean#L44-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOrderedForm.lean#L44-L71

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

theorem GlobalTheory.CompanionTheory.SegOrder.exists_ordered_form : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) →
    ∀ m : Multiset (ASeg T), ∃ L : List (ASeg T), (L : Multiset (ASeg T)) = m ∧ AOrdered s L := by sorry
