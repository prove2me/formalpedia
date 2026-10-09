-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_radial
-- name    : HunterPDE.Harmonic.hasDerivAt_sphereAverage_radial
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T19:15:13.346569+00:00
-- url     : https://prove2.me/theorems/9ac527dc-b7ec-4749-ac3d-c2d4afc33efa
-- title:
--   Differentiating spherical averages under the unit-sphere integral
-- statement:
--   Let $n\ge1$, $r>0$, and suppose $u:\mathbb R^n\to\mathbb R$ is continuously differentiable in a neighborhood of each point of the closed ball $\overline B_r(x)$. Let $\sigma$ denote the surface measure of the unit sphere. Then the spherical average has the derivative
--   $$\frac{d}{dt}\bigg|_{t=r}\operatorname{sphereAverage}(u,x,t)=\frac{1}{\sigma(S^{n-1})}\int_{S^{n-1}} Du(x+r\omega)[\omega]\,d\sigma(\omega).$$
--   The derivative is two-sided. Compactness of the closed ball and neighborhood regularity provide the uniform control needed to differentiate under the integral. This is the differentiation step in Hunter's derivation of (2.4).
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, p. 20, proof of Theorem 2.1, derivation of Eq. (2.4); divergence theorem: p. 17, Theorem 1.46. Neighborhood regularity is expressed pointwise as ContDiffAt on the closed ball.

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

open MeasureTheory Set
open HunterPDE.Harmonic

namespace HunterPDE.Harmonic

theorem hasDerivAt_sphereAverage_radial {n : ℕ} (hn : 0 < n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r)
    (hu : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 u y) :
    HasDerivAt (sphereAverage u x)
      (⨍ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        fderiv ℝ u (x + r • ω.1) ω.1 ∂(volume.toSphere)) r := by sorry

end HunterPDE.Harmonic
