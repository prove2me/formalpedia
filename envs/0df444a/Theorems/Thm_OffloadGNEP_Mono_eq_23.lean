-- Prove2me | Theorems.Thm_OffloadGNEP_Mono_eq_23
-- name    : OffloadGNEP.Mono.eq_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:39.40027+00:00
-- url     : https://prove2.me/theorems/909b008c-241d-4f63-80a8-87ee688d10a9
-- title:
--   (23), p. 14 — on K, (1/(nD))(√N‖x^δ_clet‖ − eᵀx^δ_clet) ≤ (1/(nD))δ_maxχ√N(√N − 1) ≤ (δ_max/(1 − U_max))(Nχ/n)
-- statement:
--   Assume Assumption A and the standing hypotheses, and let $x\in K$. With $D=1-\frac1n\sum_t\delta_tx_{t,clet}$, $x^\delta_{clet}=(\delta_ux_{u,clet})_u$, $e$ the all-ones vector, $\|\cdot\|$ the Euclidean norm on $\mathbb R^N$ and $\delta_{\max}=\max_u\delta_u$,
--   $$\frac1{nD}\Big(\sqrt N\|x^\delta_{clet}\|-e^\top x^\delta_{clet}\Big)\ \le\ \frac1{nD}\Big(\delta_{\max}\chi\sqrt N(\sqrt N-1)\Big)\ \le\ \frac{\delta_{\max}}{1-U_{\max}}\,\frac{N\chi}{n}.$$
--
--   Combined with (22), this shows that condition (18) of Theorem 1 forces $B^s$ to be positive semidefinite at every feasible profile.
--
--   **Formalization Note** Both inequalities are asserted, as a conjunction. $\delta_{\max}$ is the real supremum of the $\delta_u$ (the maximum when $N\ge1$; for $N=0$ every term is $0$).
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 14, (23)

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Setting

namespace OffloadGNEP.Mono

theorem eq_23 {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (x : Fin N → Tier → ℝ) (hx : x ∈ K P) :
    1 / ((P.n : ℝ) * D P x) * (Real.sqrt N * eucNorm (xdelta P x) - ∑ u, xdelta P x u) ≤
        1 / ((P.n : ℝ) * D P x) * (deltaMax P * P.chi * Real.sqrt N * (Real.sqrt N - 1)) ∧
      1 / ((P.n : ℝ) * D P x) * (deltaMax P * P.chi * Real.sqrt N * (Real.sqrt N - 1)) ≤
        deltaMax P / (1 - P.Umax) * ((N : ℝ) * P.chi / P.n) := by sorry

end OffloadGNEP.Mono
