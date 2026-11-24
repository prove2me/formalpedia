-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SegOrder_exists_sublists_interleave
-- name    : GlobalTheory.CompanionTheory.SegOrder.exists_sublists_interleave
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:20.949132+00:00
-- url     : https://prove2.me/theorems/37fb7178-d1ae-4aca-b9be-5cf96a05118c
-- title:
--   Seg Order: exists sublists interleave
-- statement:
--   The Seg Order construction uses the exists sublists interleave property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCommonOrderedForm.lean#L41-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCommonOrderedForm.lean#L41-L75

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

theorem GlobalTheory.CompanionTheory.SegOrder.exists_sublists_interleave (s : T → T) (L : List (ASeg T)) :
    ∀ m n : Multiset (ASeg T), (L : Multiset (ASeg T)) = m + n →
      ∃ L₁ L₂ : List (ASeg T), L₁.Sublist L ∧ L₂.Sublist L ∧
        (L₁ : Multiset (ASeg T)) = m ∧ (L₂ : Multiset (ASeg T)) = n ∧
        Interleave (wt s L₁) (wt s L₂) (wt s L) := by sorry
