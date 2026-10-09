-- Prove2me | Theorems.Thm_MeasureTheory_integral_directional_derivative_ball
-- name    : MeasureTheory.integral_directional_derivative_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T09:39:01.972529+00:00
-- url     : https://prove2.me/theorems/bc39bf9f-ad10-4722-aeb9-fcfb1b7a5cc1
-- title:
--   Scalar integration by parts on a Euclidean ball in a constant direction
-- statement:
--   Let $n\ge1$, $r>0$, $x\in\mathbb R^n$, and let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable in a neighborhood of each point of the closed ball $\overline B_r(x)$. For any constant vector $v\in\mathbb R^n$,
--
--   $$\int_{B_r(x)}Df(y)[v]\,dy=r^{n-1}\int_{S^{n-1}}f(x+r\omega)\langle v,\omega\rangle\,d\sigma(\omega).$$
--
--   Here $d\sigma$ is the surface measure on the unit sphere. This scalar boundary integration formula applies in every constant direction, and is useful for integration by parts, weak derivative identities, and componentwise assembly of vector or covector flux formulas.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed p. 17 Theorem 1.46 and printed p. 18 subsequent integration-by-parts formula. Specialize to the ball and the vector field f v: its divergence is Df[v], outward unit normal is omega, and surface scaling is r^(n-1).

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp

open MeasureTheory

namespace MeasureTheory

/-- Scalar integration by parts on a ball in a constant direction. -/
theorem integral_directional_derivative_ball {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hf : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 f y)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y in Metric.ball x r, fderiv ℝ f y v) =
      r ^ (n - 1) *
        (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          f (x + r • ω.1) * inner ℝ v ω.1 ∂volume.toSphere) := by sorry

end MeasureTheory
