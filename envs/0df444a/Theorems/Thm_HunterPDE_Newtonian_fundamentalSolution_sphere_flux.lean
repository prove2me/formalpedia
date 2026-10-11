-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_sphere_flux
-- name    : HunterPDE.Newtonian.fundamentalSolution_sphere_flux
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T17:47:46.092461+00:00
-- url     : https://prove2.me/theorems/565884f2-3b8e-47f9-a834-ba668c7a624f
-- title:
--   Exact Newtonian coordinate flux on every centred sphere
-- statement:
--   Let $n\ge2$, $R>0$, and let $\Gamma$ be the Newtonian fundamental solution. For every coordinate pair $i,j$,
--
--   $$R^{n-1}\int_{S^{n-1}}\partial_i\Gamma(-Rw)w_j\,dS(w)=\frac{\delta_{ij}}n.$$
--
--   The signed flux is independent of the radius. It supplies the spherical correction in the Hessian representation and the cancellation of the Hessian kernel over concentric annuli.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed p. 39, Corollary 2.27 proof, the sphere flux calculation following equation (2.29).

import Theorems.Thm_MeasureTheory_integral_sphere_coordinate_mul
import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open MeasureTheory HunterPDE.Newtonian

theorem HunterPDE.Newtonian.fundamentalSolution_sphere_flux (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : 0 < R) (i j : Fin n) :
    R ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j ∂volume.toSphere) =
      1 / (n : ℝ) * (if i = j then 1 else 0) := by sorry
