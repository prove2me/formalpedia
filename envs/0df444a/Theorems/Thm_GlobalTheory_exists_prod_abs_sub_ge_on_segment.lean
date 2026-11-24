-- Prove2me | Theorems.Thm_GlobalTheory_exists_prod_abs_sub_ge_on_segment
-- name    : GlobalTheory.exists_prod_abs_sub_ge_on_segment
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:41:34.213415+00:00
-- url     : https://prove2.me/theorems/a8a6daee-fcbd-481f-9cb2-ecd3d640de8d
-- title:
--   Global Theory: exists prod abs sub ge on segment
-- statement:
--   The Global Theory construction uses the exists prod abs sub ge on segment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsProdAbsSubGeOnSegment.lean#L8-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsProdAbsSubGeOnSegment.lean#L8-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsProdAbsSubGeOnSegment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
open Polynomial

theorem GlobalTheory.exists_prod_abs_sub_ge_on_segment : ∀ (N : ℕ) (x : Fin N → ℝ) (a δ : ℝ), 0 < δ →
    ∃ r : ℝ, a ≤ r ∧ r ≤ a + δ ∧ (δ / (2 * Real.exp 1)) ^ N ≤ ∏ i, |r - x i| := by sorry
