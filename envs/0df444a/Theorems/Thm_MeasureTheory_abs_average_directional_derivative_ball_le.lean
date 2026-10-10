-- Prove2me | Theorems.Thm_MeasureTheory_abs_average_directional_derivative_ball_le
-- name    : MeasureTheory.abs_average_directional_derivative_ball_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T14:58:01.998024+00:00
-- url     : https://prove2.me/theorems/e6b92f92-f610-468c-8710-969ae02d8b8f
-- title:
--   Boundary bounds control the ball mean of a directional derivative
-- statement:
--   Let $n\ge1$, $r>0$, and let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable near every point of $\overline B_r(x)$. If $|f(y)|\le M$ there, then for every constant vector $v$,
--
--   $$\left|\fint_{B_r(x)}Df(y)[v]\,dy\right|\le\frac nr M\|v\|.$$
--
--   No harmonicity is assumed. This is the quantitative boundary estimate in the integration-by-parts proof of interior derivative bounds.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed p. 23, proof of Theorem 2.7; mean-value identities: printed p. 20, Theorem 2.1; polar integration: printed p. 17, Proposition 1.45.

import Theorems.Thm_MeasureTheory_integral_directional_derivative_ball
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory Set
set_option autoImplicit false

theorem MeasureTheory.abs_average_directional_derivative_ball_le {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hf : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 f y)
    (v : EuclideanSpace ℝ (Fin n)) {M : ℝ}
    (hM : ∀ y ∈ Metric.closedBall x r, |f y| ≤ M) :
    |⨍ y in Metric.ball x r, fderiv ℝ f y v| ≤ (n / r) * M * ‖v‖ := by sorry
