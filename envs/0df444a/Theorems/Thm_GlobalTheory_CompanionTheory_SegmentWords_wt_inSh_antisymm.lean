-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SegmentWords_wt_inSh_antisymm
-- name    : GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:43.325701+00:00
-- url     : https://prove2.me/theorems/b9abcbb8-6270-48ef-b5e8-94ed45ef6da8
-- title:
--   Segment Words: wt in Sh antisymm
-- statement:
--   The Segment Words construction uses the wt in Sh antisymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightAntisymmetricEq.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightAntisymmetricEq.lean#L11-L20

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLtStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightAntisymmetricEq
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SegmentWords

theorem GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L M : List (ASeg T)), AOrdered s L →
    AOrdered s M → InSh s (M : Multiset (ASeg T)) (wt s L) →
    InSh s (L : Multiset (ASeg T)) (wt s M) →
    (L : Multiset (ASeg T)) = (M : Multiset (ASeg T)) := by sorry
