-- Prove2me | Theorems.Thm_MeasureTheory_average_covector_flux_ball
-- name    : MeasureTheory.average_covector_flux_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T22:47:15.066126+00:00
-- url     : https://prove2.me/theorems/ffbaa9b1-1415-490f-b887-c326ed5cfcd9
-- title:
--   Normalized divergence theorem on a Euclidean ball for covector fields
-- statement:
--   Let $n\ge1$, $r>0$, and let $A$ be a real covector field that is continuously differentiable near each point of $\overline B_r(x)$. In the coordinate orthonormal basis $(e_i)$, write $\operatorname{div}A(y)=\sum_i DA(y)[e_i][e_i]$. Then
--   $$\fint_{S^{n-1}}A(x+r\omega)[\omega]\,d\sigma(\omega)=\frac r n\fint_{B_r(x)}\operatorname{div}A(y)\,dy.$$
--   Under Euclidean duality, this is the divergence theorem for the corresponding vector field, with both integrals normalized. It applies to arbitrary covector fields; no potential or harmonicity is required. The remaining proof obligation is the ball divergence theorem and the surface/volume normalization.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed p. 17, Theorem 1.46 specialized to a ball, and printed p. 20, derivation of Eq. (2.4). Covector fields are identified with vector fields by the Euclidean inner product; the normalization uses boundary area / ball volume = n/r.

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp

open MeasureTheory

namespace MeasureTheory

theorem average_covector_flux_ball {n : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hA : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 A y) :
    (⨍ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      A (x + r • ω.1) ω.1 ∂(volume.toSphere)) =
      (r / (n : ℝ)) *
        (⨍ y in Metric.ball x r,
          ∑ i : Fin n, fderiv ℝ A y (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ i)) := by sorry

end MeasureTheory
