-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Comb_interleave_perm_append
-- name    : GlobalTheory.CompanionTheory.Comb.interleave_perm_append
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:33:39.328072+00:00
-- url     : https://prove2.me/theorems/802bfffb-fd20-4601-bb52-0b73ec017681
-- title:
--   Comb: interleave perm append
-- statement:
--   The Comb construction uses the interleave perm append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShufflePermFlatten.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShufflePermFlatten.lean#L10-L15

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShufflePermFlatten
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Comb

theorem GlobalTheory.CompanionTheory.Comb.interleave_perm_append {T : Type u} {u v w : List T} (h : Interleave u v w) :
    w.Perm (u ++ v) := by sorry
