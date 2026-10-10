-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_directional_derivative_mean_value
-- name    : HunterPDE.Harmonic.directional_derivative_mean_value
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T15:01:03.40566+00:00
-- url     : https://prove2.me/theorems/19c2bc43-e8d6-403f-8db0-610a030d97c9
-- title:
--   Directional differentiation preserves ball and sphere mean values
-- statement:
--   Let $n\ge1$, let $\Omega\subseteq\mathbb R^n$ be open, and let $u$ be continuously differentiable near every point of $\Omega$. Suppose $u$ satisfies both the ball and sphere mean-value identities on every closed ball contained in $\Omega$. For $r>0$, $\overline B_r(x)\subseteq\Omega$, and any constant vector $v$,
--
--   $$Du(x)[v]=\fint_{B_r(x)}Du(y)[v]\,dy=\fint_{\partial B_r(x)}Du(y)[v]\,dS(y).$$
--
--   This result transfers averaging identities to directional derivatives without assuming a third derivative or explicitly commuting derivatives with a Laplacian.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed p. 23, proof of Theorem 2.7; mean-value identities: printed p. 20, Theorem 2.1; polar integration: printed p. 17, Proposition 1.45.

import Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_center
import Theorems.Thm_HunterPDE_Harmonic_ball_average_eq_of_sphereAverage_eq
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FunProp

open MeasureTheory Set Filter Topology HunterPDE.Harmonic
set_option autoImplicit false

theorem HunterPDE.Harmonic.directional_derivative_mean_value {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω)
    (hu : ∀ y ∈ Ω, ContDiffAt ℝ 1 u y) (hmv : HasMeanValueProperty Ω u)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ Ω) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ u x v = (⨍ y in Metric.ball x r, fderiv ℝ u y v) ∧
      fderiv ℝ u x v = sphereAverage (fun y => fderiv ℝ u y v) x r := by sorry
