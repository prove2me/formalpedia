-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_integral_secondPartial_annulus_eq_zero
-- name    : HunterPDE.Newtonian.integral_secondPartial_annulus_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T17:58:38.800582+00:00
-- url     : https://prove2.me/theorems/2712a995-6d85-43ee-b496-0435bce93299
-- title:
--   Signed Newtonian Hessian cancellation on concentric annuli
-- statement:
--   Let $n\ge2$, let $\Gamma$ be the Newtonian fundamental solution, and let $0<r<R$. For every centre $x$ and coordinate pair $i,j$,
--
--   $$\int_{B_R(x)\setminus\overline B_r(x)}\partial_{ij}\Gamma(x-y)\,dy=0.$$
--
--   This is signed cancellation over a concentric annulus. It is the cancellation property required when comparing truncated singular integrals; a bound on the absolute value of the kernel alone does not provide it.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed pp. 43-44, equation (2.36), spherical cancellation and the truncation identities preceding equation (2.38). Annular form obtained by the divergence theorem and the exact sphere flux from Corollary 2.27.

import Theorems.Thm_MeasureTheory_mixed_green_identity_annulus
import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_sphere_flux

open MeasureTheory HunterPDE.Newtonian
open scoped ContDiff

theorem HunterPDE.Newtonian.integral_secondPartial_annulus_eq_zero (n : ℕ) (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (R r : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hrR : r < R) (i j : Fin n) :
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      secondPartial (fundamentalSolution n) i j (x - y)) = 0 := by sorry
