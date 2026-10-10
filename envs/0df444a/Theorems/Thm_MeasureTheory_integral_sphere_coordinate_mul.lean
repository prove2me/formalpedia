-- Prove2me | Theorems.Thm_MeasureTheory_integral_sphere_coordinate_mul
-- name    : MeasureTheory.integral_sphere_coordinate_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T22:59:38.54286+00:00
-- url     : https://prove2.me/theorems/39c88d1a-65a5-4feb-b0be-a904e046eafd
-- title:
--   Second coordinate moments of unit-sphere surface measure
-- statement:
--   For $n\ge1$, surface measure on the unit sphere satisfies
--
--   $$\int_{S^{n-1}}\omega_i\omega_j\,dS(\omega)=\alpha_n\delta_{ij},$$
--
--   where $\alpha_n$ is the volume of the unit ball. Equivalently, the normalized second moment is $\delta_{ij}/n$. This is the spherical symmetry computation in Hunter Corollary 2.27, p. 39. It also follows from the ball divergence theorem applied to the linear coordinate function $y\mapsto y_i$ in direction $e_j$.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, pp. 37–39, Theorem 2.26 Eqs. (2.25)–(2.28), Corollary 2.27 Eq. (2.29).

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory

theorem MeasureTheory.integral_sphere_coordinate_mul (n : ℕ) (hn : 0 < n) (i j : Fin n) :
    (∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      w.1 i * w.1 j ∂volume.toSphere) =
      HunterPDE.Newtonian.unitBallVolume n * (if i = j then 1 else 0) := by sorry
