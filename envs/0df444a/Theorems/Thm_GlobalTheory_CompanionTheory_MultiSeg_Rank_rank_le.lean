-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_rank_le
-- name    : GlobalTheory.CompanionTheory.MultiSeg.Rank.rank_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:53:30.732801+00:00
-- url     : https://prove2.me/theorems/e1628f9a-5119-4797-b010-a2940b059c14
-- title:
--   Rank: rank le
-- statement:
--   The Rank construction uses the rank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L421-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L421-L435

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Zc.Comb
open Classical
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MultiSeg GlobalTheory.CompanionTheory.MultiSeg.Rank
variable {T : Type u}

theorem GlobalTheory.CompanionTheory.MultiSeg.Rank.rank_le (s : T → T) (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {L : List (ASeg T)} {n : Multiset (ASeg T)}
    (hL : AOrdered s L) (hn : InSh s n (wt s L)) (u : T) (d : ℕ) :
    rank s n u d ≤ rank s (L : Multiset (ASeg T)) u d := by sorry
