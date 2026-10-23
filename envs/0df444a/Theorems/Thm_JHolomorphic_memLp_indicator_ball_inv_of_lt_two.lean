-- Prove2me | Theorems.Thm_JHolomorphic_memLp_indicator_ball_inv_of_lt_two
-- name    : JHolomorphic.memLp_indicator_ball_inv_of_lt_two
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T11:03:19.727195+00:00
-- url     : https://prove2.me/theorems/d330ee2c-6c3a-4dba-b79c-f7db301624f4
-- title:
--   The Cauchy kernel $1/w$ on a disc lies in $L^q$ for $1\le q<2$
-- statement:
--   Let $1\le q<2$ and $r\in\mathbb R$. The function $w\mapsto \mathbf 1_{B_r(0)}(w)\,w^{-1}$ on $\mathbb C$ belongs to $L^q(\mathbb C)$ with respect to Lebesgue measure. This is the integrability of the Cauchy kernel needed to define the Cauchy transform on $L^p$ data with $p>2$.
--
--   **Formalization Note** Stated as `MemLp ((ball (0 : ℂ) r).indicator fun w => w⁻¹) (ENNReal.ofReal q) volume`. For $r\le0$ the ball is empty and the function is $0$.
-- source:
--   Used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Lemma 2.24

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Complex.Basic

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal

/-- For `1 ≤ q < 2` and any radius `r`, the kernel `w ↦ w⁻¹` restricted to the disc `B_r(0) ⊆ ℂ` lies in `L^q(ℂ)`. -/
theorem memLp_indicator_ball_inv_of_lt_two {q : ℝ} (hq1 : 1 ≤ q) (hq2 : q < 2) (r : ℝ) :
    MemLp ((ball (0 : ℂ) r).indicator fun w : ℂ => w⁻¹) (ENNReal.ofReal q) volume := by
  sorry

end JHolomorphic
