-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_sqLen_eq
-- name    : GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:39.024893+00:00
-- url     : https://prove2.me/theorems/c9dbb3a0-a9b4-4c7d-8005-958a060ac692
-- title:
--   Rank: sq Len eq
-- statement:
--   The Rank construction uses the sq Len eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L495-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L495-L524

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

theorem GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_eq {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (P : Finset (T × ℕ))
    (m : Multiset (ASeg T)) (hm : ∀ Δ ∈ m, pairs s Δ ⊆ P) :
    sqLen m = ∑ q ∈ P, wd q.2 * rank s m q.1 q.2 := by sorry
