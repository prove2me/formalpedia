-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_sphereAverage_radial_eq_ball_laplacian
-- name    : HunterPDE.Harmonic.sphereAverage_radial_eq_ball_laplacian
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T19:16:04.831771+00:00
-- url     : https://prove2.me/theorems/1bcf2047-c91d-4140-8538-218a2d1155b4
-- title:
--   Normalized normal flux equals the scaled ball average of the Laplacian
-- statement:
--   Let $n\ge1$, $r>0$, and suppose $u:\mathbb R^n\to\mathbb R$ is twice continuously differentiable in a neighborhood of each point of $\overline B_r(x)$. Then
--   $$\frac{1}{\sigma(S^{n-1})}\int_{S^{n-1}}Du(x+r\omega)[\omega]\,d\sigma(\omega)=\frac{r}{n}\mathop{\fint}_{B_r(x)}\Delta u(y)\,dy.$$
--   This is the divergence-theorem and normalization step in Hunter's derivation of (2.4). On the boundary, $\omega$ is the outward unit normal. Surface measure scales by $r^{n-1}$, while the ratio of ball volume to boundary area is $r/n$. No harmonicity assumption is imposed.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, p. 20, proof of Theorem 2.1, derivation of Eq. (2.4); divergence theorem: p. 17, Theorem 1.46. Neighborhood regularity is expressed pointwise as ContDiffAt on the closed ball.

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

open MeasureTheory Set
open HunterPDE.Harmonic

namespace HunterPDE.Harmonic

theorem sphereAverage_radial_eq_ball_laplacian {n : ℕ} (hn : 0 < n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r)
    (hu : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 2 u y) :
    (⨍ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      fderiv ℝ u (x + r • ω.1) ω.1 ∂(volume.toSphere)) =
      (r / (n : ℝ)) *
        (⨍ y in Metric.ball x r, Laplacian.laplacian u y) := by sorry

end HunterPDE.Harmonic
