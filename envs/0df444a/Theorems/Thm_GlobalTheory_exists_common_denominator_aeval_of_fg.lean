-- Prove2me | Theorems.Thm_GlobalTheory_exists_common_denominator_aeval_of_fg
-- name    : GlobalTheory.exists_common_denominator_aeval_of_fg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:22.102012+00:00
-- url     : https://prove2.me/theorems/c0044ee7-fd34-468c-973b-801175734cce
-- title:
--   Global Theory: exists common denominator aeval of fg
-- statement:
--   The Global Theory construction uses the exists common denominator aeval of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonDenominatorAevalOfFg.lean#L15-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonDenominatorAevalOfFg.lean#L15-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonDenominatorAevalOfFg
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

theorem GlobalTheory.exists_common_denominator_aeval_of_fg (O E A : Type) [CommRing O] [IsDomain O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] (g : A) (h : ∀ x : A, ∃ p : E[X], aeval g p = x)
    (S : Submodule O A) (hS : S.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by sorry
