-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_reward_eq
-- name    : Kyprianou.Ch04.cor412_dyadic_reward_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:11:59.779734+00:00
-- url     : https://prove2.me/theorems/871bb94d-12af-4878-a426-71ce54a5a7e1
-- title:
--   Right-continuous lower-bounded path dyadic reward equals exponential of its infimum
-- statement:
--   Right-continuous lower-bounded path dyadic reward equals exponential of its infimum.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- For a lower-bounded right-continuous path, countable dyadic infima give its actual infimum. -/

theorem Kyprianou.Ch04.cor412_dyadic_reward_eq (f : NNReal → ℝ)
    (hRC : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hB : BddBelow (range f)) (β : ℝ) (hβ : 0 ≤ β) :
    (⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))) =
      ENNReal.ofReal (Real.exp (β * sInf (range f))) := by sorry
