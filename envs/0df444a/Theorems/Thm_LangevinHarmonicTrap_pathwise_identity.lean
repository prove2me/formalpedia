-- Prove2me | Theorems.Thm_LangevinHarmonicTrap_pathwise_identity
-- name    : LangevinHarmonicTrap.pathwise_identity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:11:29.978984+00:00
-- url     : https://prove2.me/theorems/5cd529b3-30d2-4ec5-a0a5-7acae5025887
-- title:
--   Langevin's rearrangement: $\tfrac{m}{2}\ddot S + \tfrac{\zeta}{2}\dot S + kS = m\dot r^2 + r\cdot f$
-- statement:
--   Part (a) of the source. Multiplying Newton's equation by $r$ and rearranging, every realization of the dynamics satisfies, with $S = r^2$, $$ \frac{m}{2}\,\ddot S(t) + \frac{\zeta}{2}\,\dot S(t) + k\,S(t) \;=\; m\,\dot r(t)^2 + r(t)\cdot f(t). $$ This is a deterministic identity, valid path by path, with no averaging and no assumption on the random force; the first and second derivatives of $S$ enter through hypotheses naming them, so the statement is exactly a differential identity in $r^2$ and $\dot r^2$.
-- source:
--   Nonequilibrium Statistical Physics, Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, Trinity Term 2018, paper A15282W1, Question 1 (parts (a), (b), (d), (e)), Eq. (1); Langevin's 1908 method, cf. D. S. Lemons and A. Gythiel, Am. J. Phys. 65 (1997) 1079, https://doi.org/10.1119/1.18725

import Mathlib
import Definitions.Def_LangevinHarmonicTrap_dotSum
import Definitions.Def_LangevinHarmonicTrap_IsLangevinPath

open Finset

namespace LangevinHarmonicTrap

theorem pathwise_identity {d : ℕ} {m zeta k : ℝ} {x v a f : Fin d → ℝ → ℝ}
    (h : IsLangevinPath d m zeta k x v a f)
    (S S1 S2 : ℝ → ℝ)
    (hS : ∀ t : ℝ, S t = dotSum d x x t)
    (hS1 : ∀ t : ℝ, HasDerivAt S (S1 t) t)
    (hS2 : ∀ t : ℝ, HasDerivAt S1 (S2 t) t) :
    ∀ t : ℝ, m / 2 * S2 t + zeta / 2 * S1 t + k * S t
      = m * dotSum d v v t + dotSum d x f t := by sorry

end LangevinHarmonicTrap
