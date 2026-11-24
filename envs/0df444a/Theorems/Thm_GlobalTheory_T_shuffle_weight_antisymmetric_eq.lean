-- Prove2me | Theorems.Thm_GlobalTheory_T_shuffle_weight_antisymmetric_eq
-- name    : GlobalTheory.T.shuffle_weight_antisymmetric_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:57:49.09795+00:00
-- url     : https://prove2.me/theorems/d6cf1e32-3991-4511-9b4c-e552fee3fe3f
-- title:
--   T: shuffle weight antisymmetric eq
-- statement:
--   The T construction uses the shuffle weight antisymmetric eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightAntisymmetricEqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightAntisymmetricEqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightAntisymmetricEq
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightAntisymmetricEqStatement
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

theorem GlobalTheory.T.shuffle_weight_antisymmetric_eq : ∀ {T : Type u} (s : T → T), Function.Injective s → (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L M : List (ASeg T)), AOrdered s L → AOrdered s M → InSh s (M : Multiset (ASeg T)) (wt s L) → InSh s (L : Multiset (ASeg T)) (wt s M) → (L : Multiset (ASeg T)) = (M : Multiset (ASeg T)) := by sorry
