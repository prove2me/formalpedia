-- Prove2me | Theorems.Thm_OffloadGNEP_Mono_theorem_1
-- name    : OffloadGNEP.Mono.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:44.339966+00:00
-- url     : https://prove2.me/theorems/f3c65b56-3d42-42b5-b69f-4be7246c4f3f
-- title:
--   Theorem 1, p. 12 — if δ_max ≤ n(1 − U_max)/(Nχ), the VI map F of the offloading GNEP is monotone on K
-- statement:
--   Consider the computation-offloading game (10)–(15) with $N$ users, $n$ cloudlet servers, offloadable fraction $\chi$ and utilisation cap $U_{\max}$, under Assumption A ($U_{\max}$ and all $\alpha_u,\delta_u$ lie in $(0,1)$) and the standing hypotheses $n\ge1$, $0<\chi\le1$. Let $K=(\prod_u\tilde K_u)\cap\Omega$ be its joint feasible set and $F$ the stacked partial gradients of the users' costs. If
--   $$\delta_{\max}\ \le\ \frac{n}{N\chi}\,(1-U_{\max}),\qquad\delta_{\max}=\max_{u=1,\dots,N}\delta_u,\tag{18}$$
--   then $F$ is monotone on $K$:
--   $$(F(y)-F(x))^\top(y-x)\ \ge\ 0\qquad\text{for all }x,y\in K.$$
--
--   Monotonicity of $F$ is what makes the variational solutions of the GNEP computable by the distributed algorithms the paper develops, and condition (18) says the cloudlet is not overloaded relative to the number of servers.
--
--   **Formalization Note** Users are indexed by `Fin N`. Monotonicity is on $K$ (footnote 3), with the Euclidean pairing over all $3N$ coordinates; $F$ is the closed form of p. 11. Condition (18) is kept in the paper's form with $\delta_{\max}$ the real supremum of the $\delta_u$; for $N=0$ Lean reads its right side as $0$ and the statement is trivial.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 12, Theorem 1, (18) and footnote 3

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Setting

namespace OffloadGNEP.Mono

theorem theorem_1 {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (h18 : deltaMax P ≤ (P.n : ℝ) / ((N : ℝ) * P.chi) * (1 - P.Umax)) :
    IsMonotoneOn (K P) (F P) := by sorry

end OffloadGNEP.Mono
