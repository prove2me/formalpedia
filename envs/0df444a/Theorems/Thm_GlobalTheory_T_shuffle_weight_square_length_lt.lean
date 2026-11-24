-- Prove2me | Theorems.Thm_GlobalTheory_T_shuffle_weight_square_length_lt
-- name    : GlobalTheory.T.shuffle_weight_square_length_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:57:30.87612+00:00
-- url     : https://prove2.me/theorems/9137a2ab-3402-4bea-9339-1549d11d75de
-- title:
--   T: shuffle weight square length lt
-- statement:
--   The T construction uses the shuffle weight square length lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLtStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLtStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLtStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.shuffle_weight_square_length_lt : ∀ {T : Type u} (s : T → T), Function.Injective s → (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L : List (ASeg T)) (n : Multiset (ASeg T)), AOrdered s L → InSh s n (wt s L) → n ≠ (L : Multiset (ASeg T)) → sqLen n < sqLen (L : Multiset (ASeg T)) := by sorry
