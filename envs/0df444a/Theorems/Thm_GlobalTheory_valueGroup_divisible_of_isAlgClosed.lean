-- Prove2me | Theorems.Thm_GlobalTheory_valueGroup_divisible_of_isAlgClosed
-- name    : GlobalTheory.valueGroup_divisible_of_isAlgClosed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:24:41.524348+00:00
-- url     : https://prove2.me/theorems/f601bfca-6397-494d-8b36-342addf536fe
-- title:
--   Global Theory: value Group divisible of is Alg Closed
-- statement:
--   The Global Theory construction uses the value Group divisible of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L220-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L220-L225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u

theorem GlobalTheory.valueGroup_divisible_of_isAlgClosed {C : Type*} [Field C] [IsAlgClosed C]
    (O : ValuationSubring C) (γ : O.ValueGroup) {n : ℕ} (hn : 0 < n) :
    ∃ δ : O.ValueGroup, δ ^ n = γ := by sorry
