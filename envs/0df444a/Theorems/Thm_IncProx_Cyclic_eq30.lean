-- Prove2me | Theorems.Thm_IncProx_Cyclic_eq30
-- name    : IncProx.Cyclic.eq30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:23.318972+00:00
-- url     : https://prove2.me/theorems/5eb37fbc-7961-4601-9719-33e0981bf64f
-- title:
--   Eq. (30) — one iteration of (19) or (20): $\|x_{k+1}-y\|^2\le\|x_k-y\|^2-2\alpha_k(F_{i_k}(z_k)-F_{i_k}(y))+\alpha_k^2c^2$
-- statement:
--   Consider problem (5)–(6) under the standing assumptions ($X$ nonempty closed convex, every $f_i$, $h_i$ real-valued convex). Take one step of iteration (19) or (20) with component $i$ and stepsize $\alpha_k>0$, from $x_k$ through $z_k$ to $x_{k+1}$, and suppose the $h_i$-subgradient used in the step satisfies $\|\tilde\nabla h_i(z_k)\|\le c$. Then for every $y\in X$,
--   $$\|x_{k+1}-y\|^2\le\|x_k-y\|^2-2\alpha_k\big(f_i(z_k)+h_i(z_k)-f_i(y)-h_i(y)\big)+\alpha_k^2c^2=\|x_k-y\|^2-2\alpha_k\big(F_i(z_k)-F_i(y)\big)+\alpha_k^2c^2.$$
--
--   This one-iteration estimate is summed over a cycle in the proof of Proposition 3.
--
--   **Formalization Note** The paper derives (30) for every $k$ of a run under (22); only the bound on $\tilde\nabla h_{i_k}(z_k)$ is used, so the statement takes a single step and that bound. $x_k$ need not lie in $X$. The middle expression equals the right one by the definition $F_i=f_i+h_i$, so the statement records the right one.
-- source:
--   Bertsekas, Incremental Proximal Methods for Large Scale Convex Optimization, LIDS-P-2847 (rev. March 2011), §3, proof of Proposition 3, p. 9, eq. (30) (from (28), (29))

import Mathlib
import Definitions.Def_IncProx_Cyclic_Basic

namespace IncProx.Cyclic

/-- Eq. (30) (§3, proof of Proposition 3, p. 9). One step of iteration (19) or (20) with
component `i` and stepsize `a > 0`, from `x` through `z` to `x'`, whose `h`-subgradient `gH` has
norm at most `c` (the part of (22) that (29) uses), satisfies for every `y ∈ X`
‖x' − y‖² ≤ ‖x − y‖² − 2a(F_i(z) − F_i(y)) + a²c². -/
theorem eq30 {n m : ℕ} (P : Problem n m) (hP : P.Standing) (A : Alg) (hA : A = .a19 ∨ A = .a20)
    (i : Fin m) (a c : ℝ) (ha : 0 < a) (x z gF gH x' : Vec n)
    (hstep : Step P A i a x z gF gH x') (hgH : ‖gH‖ ≤ c) :
    ∀ y ∈ P.X, ‖x' - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - 2 * a * (P.Fi i z - P.Fi i y) + a ^ 2 * c ^ 2 := by sorry

end IncProx.Cyclic
