-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ShuffleWords_shuffle_perm
-- name    : GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:13:38.551123+00:00
-- url     : https://prove2.me/theorems/0f2f1efe-2809-4399-a65d-369bb0059348
-- title:
--   Shuffle Words: shuffle perm
-- statement:
--   The Shuffle Words construction uses the shuffle perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleOfPerm.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleOfPerm.lean#L43-L51

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleOfPerm
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ShuffleWords
variable {T : Type u}

theorem GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm {T : Type u} (us us' : List (List T)) (w : List T)
    (h : Shuffle us w) (hp : us.Perm us') : Shuffle us' w := by sorry
