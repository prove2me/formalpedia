-- Prove2me | Theorems.Thm_IncProx_Cyclic_eq37
-- name    : IncProx.Cyclic.eq37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:36.541358+00:00
-- url     : https://prove2.me/theorems/d4561636-f2b3-4bb0-993f-95c24b1921b0
-- title:
--   Eq. (37) — one iteration of (21): extra term $2\alpha_k(f_{i_k}(x_k)-f_{i_k}(x_{k+1}))$
-- statement:
--   Consider problem (5)–(6) under the standing assumptions. Take one step of iteration (21) with component $i$ and stepsize $\alpha_k>0$: $z_k=x_k-\alpha_k\tilde\nabla h_i(x_k)$ and $x_{k+1}=P_X\big(z_k-\alpha_k\tilde\nabla f_i(x_{k+1})\big)$, and suppose $\|\tilde\nabla h_i(x_k)\|\le c$. Then for every $y\in X$,
--   $$\|x_{k+1}-y\|^2\le\|x_k-y\|^2-2\alpha_k\big(F_i(x_k)-F_i(y)\big)+\alpha_k^2c^2+2\alpha_k\big(f_i(x_k)-f_i(x_{k+1})\big).$$
--
--   This is the analogue of (30) for iteration (21); the extra last term is what changes $\beta$ from $\frac1m+4$ to $\frac5m+4$ in Proposition 3.
--
--   **Formalization Note** The paper derives (37) for every $k\ge0$ of a run under (24); only the bound on $\tilde\nabla h_{i_k}(x_k)$ is used, so the statement takes a single step and that bound. The paper's first line, $\|x_k-y\|^2-2\alpha_k(f_i(x_{k+1})+h_i(x_k)-f_i(y)-h_i(y))+\alpha_k^2c^2$, equals the right-hand side above by $F_i=f_i+h_i$.
-- source:
--   Bertsekas, Incremental Proximal Methods for Large Scale Convex Optimization, LIDS-P-2847 (rev. March 2011), §3, proof of Proposition 3, p. 11, eq. (37) (from (35), (36), p. 10)

import Mathlib
import Definitions.Def_IncProx_Cyclic_Basic

namespace IncProx.Cyclic

/-- Eq. (37) (§3, proof of Proposition 3, p. 11). One step of iteration (21) with component `i`
and stepsize `a > 0`, from `x` through `z` to `x'`, whose `h`-subgradient `gH` has norm at most `c`
(the part of (24) that (35) uses), satisfies for every `y ∈ X`
‖x' − y‖² ≤ ‖x − y‖² − 2a(F_i(x) − F_i(y)) + a²c² + 2a(f_i(x) − f_i(x')). -/
theorem eq37 {n m : ℕ} (P : Problem n m) (hP : P.Standing)
    (i : Fin m) (a c : ℝ) (ha : 0 < a) (x z gF gH x' : Vec n)
    (hstep : Step P .a21 i a x z gF gH x') (hgH : ‖gH‖ ≤ c) :
    ∀ y ∈ P.X, ‖x' - y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 - 2 * a * (P.Fi i x - P.Fi i y) + a ^ 2 * c ^ 2 + 2 * a * (P.f i x - P.f i x') := by sorry

end IncProx.Cyclic
