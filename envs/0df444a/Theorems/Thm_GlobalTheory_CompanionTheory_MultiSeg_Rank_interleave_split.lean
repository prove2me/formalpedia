-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_interleave_split
-- name    : GlobalTheory.CompanionTheory.MultiSeg.Rank.interleave_split
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:53:11.772803+00:00
-- url     : https://prove2.me/theorems/9418dab5-70ab-4ae5-9e90-3103be705eaa
-- title:
--   Rank: interleave split
-- statement:
--   The Rank construction uses the interleave split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L116-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L116-L130

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

theorem GlobalTheory.CompanionTheory.MultiSeg.Rank.interleave_split : ∀ (D w' u v : List T), Interleave u v (D ++ w') →
    ∃ u1 u2 v1 v2, u = u1 ++ u2 ∧ v = v1 ++ v2 ∧ Interleave u1 v1 D ∧ Interleave u2 v2 w' := by sorry
