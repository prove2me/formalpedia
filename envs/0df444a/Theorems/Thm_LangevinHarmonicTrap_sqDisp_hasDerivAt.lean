-- Prove2me | Theorems.Thm_LangevinHarmonicTrap_sqDisp_hasDerivAt
-- name    : LangevinHarmonicTrap.sqDisp_hasDerivAt
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:09:52.407877+00:00
-- url     : https://prove2.me/theorems/78a6e65e-e528-4cbf-b4f9-e845350efd2b
-- title:
--   First and second time derivatives of $r^2$ along a path
-- statement:
--   The kinematic half of part (a): along any path of the model, the squared displacement $S = r^2$ is twice differentiable with $$ \dot S = 2\, r\cdot\dot r, \qquad \ddot S = 2\bigl(\dot r^2 + r\cdot\ddot r\bigr), $$ which is the identity that lets $r\cdot\ddot r$ be traded for $\tfrac12\ddot S - \dot r^2$ in Newton's equation.
-- source:
--   Nonequilibrium Statistical Physics, Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, Trinity Term 2018, paper A15282W1, Question 1 (parts (a), (b), (d), (e)), Eq. (1); Langevin's 1908 method, cf. D. S. Lemons and A. Gythiel, Am. J. Phys. 65 (1997) 1079, https://doi.org/10.1119/1.18725

import Mathlib
import Definitions.Def_LangevinHarmonicTrap_dotSum
import Definitions.Def_LangevinHarmonicTrap_IsLangevinPath

open Finset

namespace LangevinHarmonicTrap

theorem sqDisp_hasDerivAt {d : ℕ} {m zeta k : ℝ} {x v a f : Fin d → ℝ → ℝ}
    (h : IsLangevinPath d m zeta k x v a f) :
    (∀ t : ℝ, HasDerivAt (dotSum d x x) (2 * dotSum d x v t) t) ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => 2 * dotSum d x v s)
        (2 * (dotSum d v v t + dotSum d x a t)) t) := by sorry

end LangevinHarmonicTrap
