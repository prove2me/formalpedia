-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_secondPartial_formula
-- name    : HunterPDE.Newtonian.secondPartial_formula
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T17:40:01.185904+00:00
-- url     : https://prove2.me/theorems/fb3666e6-73b8-4325-9edb-95c623870ba1
-- title:
--   Explicit Newtonian Hessian away from the origin
-- statement:
--   Let $n\ge2$, let $\Gamma$ be the Newtonian fundamental solution with $-\Delta\Gamma=\delta_0$, and write $\alpha_n=|B_1(0)|$. For coordinate indices $i,j$ and $z\ne0$,
--
--   $$\partial_{ij}\Gamma(z)=-\frac{1}{n\alpha_n}\left(|z|^{-n}\delta_{ij}-n|z|^{-n-2}z_i z_j\right).$$
--
--   This formula identifies the singular kernel used in Newtonian potential estimates and allows its smoothness and derivative bounds to be derived by ordinary calculus.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed p. 43, equation (2.36). The source defines K_ij=-partial_ij Gamma; this statement gives partial_ij Gamma with the corresponding opposite sign.

import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open HunterPDE.Newtonian Filter
open scoped Topology

theorem HunterPDE.Newtonian.secondPartial_formula (n : ℕ) (hn : 2 ≤ n) (i j : Fin n)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) :
    secondPartial (fundamentalSolution n) i j z =
      -(1 / ((n : ℝ) * unitBallVolume n)) *
        (‖z‖ ^ (-(n : ℝ)) * (if i = j then 1 else 0) -
          (n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 2) * z i * z j) := by sorry
