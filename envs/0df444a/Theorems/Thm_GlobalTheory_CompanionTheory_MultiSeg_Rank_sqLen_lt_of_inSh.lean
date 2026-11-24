-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_sqLen_lt_of_inSh
-- name    : GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:46.790081+00:00
-- url     : https://prove2.me/theorems/bfd2266c-5e2f-4ff9-a879-05165b0c7248
-- title:
--   Rank: sq Len lt of in Sh
-- statement:
--   The Rank construction uses the sq Len lt of in Sh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L603-L639
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L603-L639

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

theorem GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh {T : Type u} (s : T → T) (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (L : List (ASeg T)) (n : Multiset (ASeg T))
    (hL : AOrdered s L) (hn : InSh s n (wt s L)) (hne : n ≠ (L : Multiset (ASeg T))) :
    sqLen n < sqLen (L : Multiset (ASeg T)) := by sorry
