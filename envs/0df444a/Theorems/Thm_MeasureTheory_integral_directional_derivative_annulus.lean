-- Prove2me | Theorems.Thm_MeasureTheory_integral_directional_derivative_annulus
-- name    : MeasureTheory.integral_directional_derivative_annulus
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T12:09:17.597793+00:00
-- url     : https://prove2.me/theorems/060f3374-d7a9-40f1-81dd-87094e5d3e27
-- title:
--   Scalar boundary integration formula on a spherical annulus in a constant direction
-- statement:
--   Let $n\ge1$, $x\in\mathbb R^n$ and $0<r<R$, and let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable in a neighbourhood of every point of the punctured closed ball $\overline B_R(x)\setminus\{x\}$. Put $A=B_R(x)\setminus\overline B_r(x)$. For every constant vector $v\in\mathbb R^n$,
--
--   $$\int_A Df(y)[v]\,dy=R^{n-1}\int_{S^{n-1}}f(x+R\omega)\langle v,\omega\rangle\,d\sigma(\omega)-r^{n-1}\int_{S^{n-1}}f(x+r\omega)\langle v,\omega\rangle\,d\sigma(\omega).$$
--
--   Here $d\sigma$ is the surface measure on the unit sphere. The outward unit normal of the annulus is $\omega$ on the outer sphere and $-\omega$ on the inner sphere. No assumption is made on $f$ at the centre $x$, so the formula applies to kernels with a singularity at the centre, such as $y\mapsto K(x-y)$ for $K$ smooth away from the origin.
--
--   **Formalization Note.** Ambient space `EuclideanSpace ℝ (Fin n)`; the regularity hypothesis is `ContDiffAt ℝ 1 f y` at each `y ∈ closedBall x R` with `y ≠ x`; the derivative is the Fréchet derivative `fderiv ℝ f y v`; the boundary is parametrized by the unit sphere with Mathlib's `volume.toSphere`, and $r^{n-1}$, $R^{n-1}$ are the surface scaling factors.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed p. 17 Theorem 1.46 and printed p. 18 subsequent integration-by-parts formula, specialized to the annulus B_R(x) minus the closed ball of radius r and the vector field f v; used for Eq. (2.27), printed pp. 37-38.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory

namespace MeasureTheory

/-- Scalar boundary integration formula on a spherical annulus in a constant direction, for a
function that is `C¹` on the closed ball punctured at its centre. -/
theorem integral_directional_derivative_annulus {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : ∀ y ∈ Metric.closedBall x R, y ≠ x → ContDiffAt ℝ 1 f y)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y in Metric.ball x R \ Metric.closedBall x r, fderiv ℝ f y v) =
      R ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + R • ω.1) * inner ℝ v ω.1 ∂volume.toSphere)
        - r ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + r • ω.1) * inner ℝ v ω.1 ∂volume.toSphere) := by sorry

end MeasureTheory
