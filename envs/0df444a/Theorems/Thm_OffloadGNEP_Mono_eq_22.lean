-- Prove2me | Theorems.Thm_OffloadGNEP_Mono_eq_22
-- name    : OffloadGNEP.Mono.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:43.824566+00:00
-- url     : https://prove2.me/theorems/9634b141-3e29-4a7e-b05b-dd5f34fa476c
-- title:
--   (22), p. 14 — (1/(nD))(√N‖x^δ_clet‖ − eᵀx^δ_clet) ≤ 1 implies Bˢ ⪰ 0
-- statement:
--   Assume Assumption A and the standing hypotheses, and let $x\in\mathbb R^{3N}$ with $D=1-\frac1n\sum_t\delta_tx_{t,clet}>0$. With $x^\delta_{clet}=(\delta_ux_{u,clet})_u$, $e$ the all-ones vector and $\|\cdot\|$ the Euclidean norm on $\mathbb R^N$, if
--   $$\frac1{nD}\Big(\sqrt N\,\|x^\delta_{clet}\|-e^\top x^\delta_{clet}\Big)\ \le\ 1,$$
--   then the symmetric part $B^s$ of the clet-block of the Jacobian is positive semidefinite.
--
--   This is the sufficient condition to which the proof of Theorem 1 reduces the semidefiniteness of $B^s$; it is then verified on the feasible region by (23).
--
--   **Formalization Note** The condition is stated at an arbitrary profile with $D>0$, as on the page; no sign condition on $x$ is assumed (the brief suggested $x_{u,clet}\ge0$, which the page does not attach to (22) and the claim does not need). Positive semidefiniteness is Mathlib's `Matrix.PosSemidef` for the real symmetric matrix $B^s$.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 14, (22)

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Setting

namespace OffloadGNEP.Mono

theorem eq_22 {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (x : Fin N → Tier → ℝ) (hD : 0 < D P x)
    (h22 : 1 / ((P.n : ℝ) * D P x) *
      (Real.sqrt N * eucNorm (xdelta P x) - ∑ u, xdelta P x u) ≤ 1) :
    (Bs P x).PosSemidef := by sorry

end OffloadGNEP.Mono
