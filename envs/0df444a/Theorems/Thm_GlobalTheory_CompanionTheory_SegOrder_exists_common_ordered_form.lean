-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SegOrder_exists_common_ordered_form
-- name    : GlobalTheory.CompanionTheory.SegOrder.exists_common_ordered_form
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:28:31.151521+00:00
-- url     : https://prove2.me/theorems/2059bf11-af31-4c31-8c80-ac8319f57c49
-- title:
--   Seg Order: exists common ordered form
-- statement:
--   The Seg Order construction uses the exists common ordered form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCommonOrderedForm.lean#L77-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCommonOrderedForm.lean#L77-L87

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOrderedForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCommonOrderedForm
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

theorem GlobalTheory.CompanionTheory.SegOrder.exists_common_ordered_form : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) →
    ∀ m n : Multiset (ASeg T), ∃ L₁ L₂ L : List (ASeg T),
      (L₁ : Multiset (ASeg T)) = m ∧ (L₂ : Multiset (ASeg T)) = n ∧
      (L : Multiset (ASeg T)) = m + n ∧ AOrdered s L₁ ∧ AOrdered s L₂ ∧ AOrdered s L ∧
      Interleave (wt s L₁) (wt s L₂) (wt s L) := by sorry
