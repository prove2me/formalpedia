-- Prove2me | Theorems.Thm_GlobalTheory_exists_absoluteValue_of_isDiscreteValuationRing
-- name    : GlobalTheory.exists_absoluteValue_of_isDiscreteValuationRing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:29:37.261384+00:00
-- url     : https://prove2.me/theorems/0b30dede-3f72-4b09-999e-69ef75941293
-- title:
--   Global Theory: exists absolute Value of is Discrete Valuation Ring
-- statement:
--   The Global Theory construction uses the exists absolute Value of is Discrete Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L310-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L310-L339

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
open IsDedekindDomain

theorem GlobalTheory.exists_absoluteValue_of_isDiscreteValuationRing (V K : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    {a : V} (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) :
    ∃ w : AbsoluteValue K ℝ, IsNonarchimedean w ∧
      (∀ x : K, w x ≤ 1 ↔ x ∈ (algebraMap V K).range) ∧ w (algebraMap V K a) = r := by sorry
