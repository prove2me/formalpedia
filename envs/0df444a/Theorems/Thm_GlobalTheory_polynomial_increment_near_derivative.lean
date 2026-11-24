-- Prove2me | Theorems.Thm_GlobalTheory_polynomial_increment_near_derivative
-- name    : GlobalTheory.polynomial_increment_near_derivative
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:01.4553+00:00
-- url     : https://prove2.me/theorems/fafa9d40-ffc9-4a44-996d-e00e69559497
-- title:
--   Global Theory: polynomial increment near derivative
-- statement:
--   The Global Theory construction uses the polynomial increment near derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RiemannSumOfOneSidedIncrements.lean#L7-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RiemannSumOfOneSidedIncrements.lean#L7-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannSumOfOneSidedIncrements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.polynomial_increment_near_derivative (s : Polynomial ℝ) {η δ : ℝ}
    (hδ : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, dist x y < δ →
      dist (s.derivative.eval x) (s.derivative.eval y) < η)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hba : b - a < δ) :
    (b - a) * s.derivative.eval a ≤ s.eval b - s.eval a + η * (b - a) ∧
    s.eval b - s.eval a ≤ (b - a) * s.derivative.eval b + η * (b - a) := by sorry
