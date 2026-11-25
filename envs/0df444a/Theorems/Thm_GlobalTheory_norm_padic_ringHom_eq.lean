-- Prove2me | Theorems.Thm_GlobalTheory_norm_padic_ringHom_eq
-- name    : GlobalTheory.norm_padic_ringHom_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:54.612895+00:00
-- url     : https://prove2.me/theorems/69c0b914-95c0-5ec7-b8d3-f3bec7d71c01
-- title:
--   Global Theory: norm padic ring Hom eq
-- statement:
--   The Global Theory construction uses the norm padic ring Hom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L422-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L422-L440

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

theorem GlobalTheory.norm_padic_ringHom_eq {C : Type*} [NormedField C] (p : ℕ) [hp : Fact p.Prime]
    (h : ‖(p : C)‖ = (p : ℝ)⁻¹) (j : ℚ_[p] →+* C) (hj : ∀ x : ℤ_[p], ‖j x‖ ≤ 1) (x : ℚ_[p]) :
    ‖j x‖ = ‖x‖ := by sorry
