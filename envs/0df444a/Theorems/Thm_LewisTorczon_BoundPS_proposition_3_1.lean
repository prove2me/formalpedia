-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_proposition_3_1
-- name    : LewisTorczon.BoundPS.proposition_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:44:36.66908+00:00
-- url     : https://prove2.me/theorems/09bc3dd8-ee72-46ef-9787-dba2f6949ca6
-- title:
--   Proposition 3.1 (6) and (8) — $\|q(x)\|\le\|g(x)\|$, and $x$ is stationary iff $q(x)=0$
-- statement:
--   Let $\Omega=\{\ell\le x\le u\}$ with $\ell_j<u_j$ for all $j$ (entries may be $\pm\infty$), let $P$ be the projection onto $\Omega$, $g=\nabla f$, and $q(x)=P(x-g(x))-x$. For every $x\in\Omega$:
--   1. $$\|q(x)\|\le\|g(x)\| ;$$
--   2. $x$ is a stationary point of $\min\{f(x):x\in\Omega\}$, i.e. $\langle g(x),z-x\rangle\ge0$ for all $z\in\Omega$, if and only if $q(x)=0$.
--
--   This justifies $\|q(x_k)\|$ as the measure of stationarity in the convergence theorems: driving it to zero is the bound constrained analogue of driving the gradient to zero.
--
--   **Formalization Note** Only parts (6) and (8) of the proposition are stated. Part (7), $\|q(x)\|\le\|P(g(x))\|$, uses $P$ for the projected gradient of Calamai and Moré rather than for the projection onto $\Omega$ defined in §1, and the paper does not define that second meaning; it is left out. The gradient is Mathlib's `gradient f x` (equal to $0$ where $f$ is not differentiable, in which case both sides of (8) hold); no smoothness is assumed, as on the page.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 5, Proposition 3.1, (6) and (8)

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Proposition 3.1** (6) and (8), p. 5: for `x ∈ Ω`, `‖q(x)‖ ≤ ‖g(x)‖`, and `x` is a stationary
point of problem (1) iff `q(x) = 0`. (Part (7) is not stated.) -/
theorem proposition_3_1 {n : ℕ} (lo hi : Fin n → EReal) (hlohi : ∀ j, lo j < hi j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ box lo hi) :
    ‖projQ lo hi f x‖ ≤ ‖gradient f x‖ ∧ (IsStationary lo hi f x ↔ projQ lo hi f x = 0) := by sorry

end LewisTorczon.BoundPS
