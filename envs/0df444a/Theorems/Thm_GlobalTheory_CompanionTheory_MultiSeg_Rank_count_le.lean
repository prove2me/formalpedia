-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_count_le
-- name    : GlobalTheory.CompanionTheory.MultiSeg.Rank.count_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:53:01.22162+00:00
-- url     : https://prove2.me/theorems/a4e4f479-d86f-4436-beef-61e1e7e6fb3d
-- title:
--   Rank: count le
-- statement:
--   The Rank construction uses the count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L302-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L302-L416

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

theorem GlobalTheory.CompanionTheory.MultiSeg.Rank.count_le (s : T → T) (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) : ∀ (B : List (ASeg T)),
    B.Pairwise (fun a b => ¬ APrecedes s b a) →
    ∀ (us : List (List T)), Shuffle us (B.map (ASeg.dec s)).flatten →
    (∀ x ∈ us, ∃ t l, x = word s t l) → ∀ (u : T) (d : ℕ),
    us.countP (fun x => decide (Con s u d x)) ≤
      B.countP (fun Γ => decide (Con s u d (Γ.dec s))) := by sorry
