-- Prove2me | Theorems.Thm_GlobalTheory_exists_padic_isometry
-- name    : GlobalTheory.exists_padic_isometry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:15.366169+00:00
-- url     : https://prove2.me/theorems/e674b748-e987-49dd-84c2-607643e77e41
-- title:
--   Global Theory: exists padic isometry
-- statement:
--   The Global Theory construction uses the exists padic isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L398-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L398-L420

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

theorem GlobalTheory.exists_padic_isometry {C : Type*} [NormedField C] [IsUltrametricDist C] [CharZero C]
    [CompleteSpace C] (p : ℕ) [Fact p.Prime] (h : ‖(p : C)‖ = (p : ℝ)⁻¹) :
    ∃ j : ℚ_[p] →+* C, ∀ x, ‖j x‖ = ‖x‖ := by sorry
