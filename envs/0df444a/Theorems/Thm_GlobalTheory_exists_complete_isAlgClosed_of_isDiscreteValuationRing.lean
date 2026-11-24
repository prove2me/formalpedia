-- Prove2me | Theorems.Thm_GlobalTheory_exists_complete_isAlgClosed_of_isDiscreteValuationRing
-- name    : GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:42.275807+00:00
-- url     : https://prove2.me/theorems/2d63cd22-f910-4ee2-8100-15054b2cfeb3
-- title:
--   Global Theory: exists complete is Alg Closed of is Discrete Valuation Ring
-- statement:
--   The Global Theory construction uses the exists complete is Alg Closed of is Discrete Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L341-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L341-L363

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

theorem GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing (V : Type*) (K : Type u)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (_ : Algebra K C),
      (∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range) ∧
        ‖algebraMap K C (algebraMap V K a)‖ = r := by sorry
