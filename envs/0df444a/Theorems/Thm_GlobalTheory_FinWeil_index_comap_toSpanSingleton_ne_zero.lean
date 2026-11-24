-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_index_comap_toSpanSingleton_ne_zero
-- name    : GlobalTheory.FinWeil.index_comap_toSpanSingleton_ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:26:01.090482+00:00
-- url     : https://prove2.me/theorems/50e9bb43-76a3-4fd2-b2ac-de951b6fd91e
-- title:
--   Fin Weil: index comap to Span Singleton ne zero
-- statement:
--   The Fin Weil construction uses the index comap to Span Singleton ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsAdjacentSelfDualLatticeToward.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsAdjacentSelfDualLatticeToward.lean#L9-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PerfectPairingQuotients
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsAdjacentSelfDualLatticeToward
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil

theorem GlobalTheory.FinWeil.index_comap_toSpanSingleton_ne_zero {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) {y : X} (hy : y ∈ B) :
    (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index ≠ 0 := by sorry
