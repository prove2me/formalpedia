-- Prove2me | Theorems.Thm_KAdaptability_EpsApprox_proposition_1
-- name    : KAdaptability.EpsApprox.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:00:52.686306+00:00
-- url     : https://prove2.me/theorems/2c242e59-7326-4be1-b9f4-0523f2f24b39
-- title:
--   Proposition 1 — the K-adaptability problem 𝒫_K is equivalent to problem (6)
-- statement:
--   Let an instance of the two-stage robust binary program with constraint uncertainty be given, with $\mathcal X\subseteq\{0,1\}^N$, $\mathcal Y\subseteq\{0,1\}^M$ and $\Xi=\{\xi:A\xi\le b\}$ nonempty and bounded, and let $K\in\mathbb N$. For $\ell\in\mathcal L=\{0,\dots,L\}^K$ let $\Xi(\ell)$ be the set of parameters $\xi\in\Xi$ for which every policy $y^k$ with $\ell_k=0$ satisfies $Tx+Wy^k\le H\xi$ and every policy with $\ell_k\ne0$ violates constraint $\ell_k$.
--
--   Then for every decision $(x,\{y^k\}_{k\in\mathcal K})\in\mathcal X\times\mathcal Y^K$,
--   $$\sup_{\xi\in\Xi}\Big[\xi^\top Cx+\inf_{k\in\mathcal K}\{\xi^\top Qy^k : Tx+Wy^k\le H\xi\}\Big]
--   =\sup_{\ell\in\mathcal L}\ \sup_{\xi\in\Xi(\ell)}\Big[\xi^\top Cx+\min_{k\in\mathcal K:\ \ell_k=0}\xi^\top Qy^k\Big],$$
--   as extended real numbers. Consequently the K-adaptability problem $\mathcal P_K$ and problem (6) have the same feasible decisions, the same objective value at every decision, and the same optimal value.
--
--   This reformulation moves the second-stage constraints from the objective of $\mathcal P_K$ into a finite family of decision-dependent uncertainty sets; it is the problem that the ε-approximations $(6_\varepsilon)$ approximate.
--
--   **Formalization Note** The paper's "is equivalent to" is pinned down as equality of the two objective functions at every decision, in `EReal`, with empty infima equal to $+\infty$ (the paper's convention for $\mathcal P_K$ on p. 8).
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 16, Proposition 1; proof pp. ec5–ec6 (PDF pp. 39–40)

import Mathlib
import Definitions.Def_KAdaptability_EpsApprox_Approx

namespace KAdaptability.EpsApprox

open Problem

/-- **Proposition 1** (p. 16). The K-adaptability problem 𝒫_K is equivalent to problem (6):
for every decision `(x, {y^k}_{k∈𝒦}) ∈ 𝒳 × 𝒴^K`, the objective value of 𝒫_K equals the
objective value of (6), as extended reals. -/
theorem proposition_1 {N M L nQ R K : ℕ} (P : Problem N M L nQ R)
    (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (hd : P.IsDecision x y) :
    P.objPK x y = P.obj6 x y := by sorry

end KAdaptability.EpsApprox
