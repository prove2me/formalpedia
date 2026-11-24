-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_mem_of_rank
-- name    : GlobalTheory.CompanionTheory.MultiSeg.Rank.mem_of_rank
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:53:21.719809+00:00
-- url     : https://prove2.me/theorems/5269e3a9-e07b-42c2-a575-1ba022801b9b
-- title:
--   Rank: mem of rank
-- statement:
--   The Rank construction uses the mem of rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L540-L560
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L540-L560

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

theorem GlobalTheory.CompanionTheory.MultiSeg.Rank.mem_of_rank {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {a b : Multiset (ASeg T)} {Δ : ASeg T}
    (hΔ : Δ ∈ a) (hb : ∀ Γ ∈ b, Γ.len ≤ Δ.len)
    (h : rank s a Δ.start (Δ.len - 1) = rank s b Δ.start (Δ.len - 1)) : Δ ∈ b := by sorry
