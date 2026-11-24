-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_shuffle_split
-- name    : GlobalTheory.CompanionTheory.MultiSeg.Rank.shuffle_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:29.753847+00:00
-- url     : https://prove2.me/theorems/4d790a63-7bbe-4105-936b-002f50a3a3a9
-- title:
--   Rank: shuffle split
-- statement:
--   The Rank construction uses the shuffle split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L132-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L132-L151

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

theorem GlobalTheory.CompanionTheory.MultiSeg.Rank.shuffle_split : ∀ (us : List (List T)) (D w' : List T), Shuffle us (D ++ w') →
    ∃ P : List (List T × List T), P.map (fun p => p.1 ++ p.2) = us ∧
      Shuffle (P.map Prod.fst) D ∧ Shuffle (P.map Prod.snd) w' := by sorry
