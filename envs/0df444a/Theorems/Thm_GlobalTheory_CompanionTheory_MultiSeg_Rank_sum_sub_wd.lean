-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_sum_sub_wd
-- name    : GlobalTheory.CompanionTheory.MultiSeg.Rank.sum_sub_wd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:37.975915+00:00
-- url     : https://prove2.me/theorems/4b8e04a2-4240-434f-bcec-71422b80a489
-- title:
--   Rank: sum sub wd
-- statement:
--   The Rank construction uses the sum sub wd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L446-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L446-L457

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

theorem GlobalTheory.CompanionTheory.MultiSeg.Rank.sum_sub_wd (l : ℕ) : ∑ d ∈ Finset.range l, (l - d) * wd d = l ^ 2 := by sorry
