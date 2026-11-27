-- Prove2me | Theorems.Thm_GlobalTheory_T_perm_flatten_of_shuffle
-- name    : GlobalTheory.T.perm_flatten_of_shuffle
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:42.708446+00:00
-- url     : https://prove2.me/theorems/148a5bc0-6c62-5cf8-9ce2-1e629efb742e
-- title:
--   T: perm flatten of shuffle
-- statement:
--   The T construction uses the perm flatten of shuffle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShufflePermFlattenStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShufflePermFlattenStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShufflePermFlatten
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShufflePermFlattenStatement
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

theorem GlobalTheory.T.perm_flatten_of_shuffle : ∀ {T : Type u} (us : List (List T)) (w : List T), Shuffle us w → w.Perm us.flatten := by sorry
