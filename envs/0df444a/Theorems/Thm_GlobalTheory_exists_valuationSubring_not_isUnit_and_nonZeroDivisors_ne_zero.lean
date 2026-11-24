-- Prove2me | Theorems.Thm_GlobalTheory_exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero
-- name    : GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:45:29.585165+00:00
-- url     : https://prove2.me/theorems/835d58c7-411d-4673-b7e1-1d019dcae47a
-- title:
--   Global Theory: exists valuation Subring not is Unit and non Zero Divisors ne zero
-- statement:
--   The Global Theory construction uses the exists valuation Subring not is Unit and non Zero Divisors ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsValuationSubringAlgClosedNotIsUnit.lean#L7-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsValuationSubringAlgClosedNotIsUnit.lean#L7-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsValuationSubringAlgClosedNotIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory

theorem GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero :
    ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u →
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V),
        ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by sorry
