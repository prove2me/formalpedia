-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_sum_pairs
-- name    : GlobalTheory.CompanionTheory.MultiSeg.Rank.sum_pairs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:36.084381+00:00
-- url     : https://prove2.me/theorems/7a8d037b-2f09-48bb-8498-989af9d92cf4
-- title:
--   Rank: sum pairs
-- statement:
--   The Rank construction uses the sum pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L479-L493
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L479-L493

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

theorem GlobalTheory.CompanionTheory.MultiSeg.Rank.sum_pairs {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (Δ : ASeg T) :
    ∑ q ∈ pairs s Δ, wd q.2 = Δ.len ^ 2 := by sorry
