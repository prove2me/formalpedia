-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalCommonRetainedAtomJumpLedgerV1
-- name    : Kyprianou.Ch04.physicalCommonRetainedAtomJumpLedgerV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T10:47:41.465928+00:00
-- url     : https://prove2.me/theorems/e4b388b8-6e1a-4ee2-9c19-aeb1c2145ea1
-- title:
--   Exact physical nonlinear jump ledger for a finite cutoff
-- statement:
--   The nonlinear jump sum is the exact physical remainder plus the large-mark and small-mark weighted linear sums, by partitioning the retained atoms.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem physicalCommonRetainedAtomJumpLedgerV1 (R : Measure (ℝ × ℝ)) (T : NNReal) (e : ℝ)
    (he : e < 1) (S : Finset NNReal) (j : NNReal → ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ e < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (Y L : NNReal → ℝ) (f fx : ℝ → ℝ → ℝ)
    (hJ : ∀ r ∈ S, Y r = L r + j r) :
    (∑ r ∈ S, (f r (Y r) - f r (L r))) =
      (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|},
        (f z.1 (L z.1.toNNReal + z.2) - f z.1 (L z.1.toNNReal) -
          z.2 * fx z.1 (L z.1.toNNReal)) ∂ R) +
      (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * fx z.1 (L z.1.toNNReal) ∂ R) +
      (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
        z.2 * fx z.1 (L z.1.toNNReal) ∂ R) := by
  sorry
end Kyprianou.Ch04
