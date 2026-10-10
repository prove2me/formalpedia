-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_norm_secondPartial_le
-- name    : HunterPDE.Newtonian.norm_secondPartial_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T10:09:20.073519+00:00
-- url     : https://prove2.me/theorems/b7dba333-0490-43e9-a126-9773e7e95598
-- title:
--   The Newtonian Hessian has critical radial growth away from the origin
-- statement:
--   Let $n\ge2$ and let $\Gamma$ be the Newtonian fundamental solution with the sign convention $-\Delta\Gamma=\delta$. For any coordinate indices $i,j$, there is a finite nonnegative constant $C$ such that
--
--   $$|\partial_{ij}\Gamma(z)|\le C|z|^{-n}\qquad\text{for every }z\ne0.$$
--
--   This is the punctured Hessian growth bound used in the cancellation integrability step of Hunter's Newtonian second-derivative representation.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed p. 33 Eq. (2.14) and p. 38 Theorem 2.26 Eq. (2.27); radial growth estimate obtained by differentiating the displayed Newtonian gradient.

import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open HunterPDE.Newtonian

theorem HunterPDE.Newtonian.norm_secondPartial_le (n : ℕ) (hn : 2 ≤ n) (i j : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
      ‖secondPartial (fundamentalSolution n) i j z‖ ≤ C * ‖z‖ ^ (-(n : ℝ)) := by sorry
