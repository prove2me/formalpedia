-- Prove2me | Theorems.Thm_KAdaptability_Bilinear_theorem_5
-- name    : KAdaptability.Bilinear.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:06:13.421168+00:00
-- url     : https://prove2.me/theorems/35612415-ba60-43a4-bdba-bac224b428c9
-- title:
--   Theorem 5 — the ε-approximation (6_ε) is equivalent to the mixed-integer bilinear program (7)
-- statement:
--   Consider the two-stage robust binary program with uncertain constraints: data $C,Q,T,W,H$, an uncertainty set $\Xi=\{\xi\in\mathbb R^Q:A\xi\le b\}$ that is nonempty and bounded, $\mathcal X\subseteq\{0,1\}^N$, $\mathcal Y\subseteq\{0,1\}^M$, and $K$ second-stage policies. Fix $\epsilon>0$, and let $\varphi_\epsilon$ be the objective of the approximate problem
--   $$(6_\epsilon)\qquad \min_{x\in\mathcal X,\ y^k\in\mathcal Y}\ \sup_{\ell\in\mathcal L}\ \sup_{\xi\in\Xi_\epsilon(\ell)}\Big[\xi^\top Cx+\min_{k:\ \ell_k=0}\xi^\top Qy^k\Big].$$
--   Theorem 5 states that $(6_\epsilon)$ is equivalent to the mixed-integer bilinear program (7), which minimizes $\tau$ subject to $x\in\mathcal X$, $y^k\in\mathcal Y$, $\tau\in\mathbb R$, and for each $\ell\in\partial\mathcal L$ (resp. $\ell\in\mathcal L_+$) the dual constraints on $\lambda(\ell)\in\Delta_K(\ell)$, $\alpha(\ell)$, $\beta^k(\ell)$, $\gamma(\ell)$ (resp. $\alpha(\ell)$, $\gamma(\ell)$) described in the definition of program (7).
--
--   Precisely:
--
--   1. for every decision $(x,\{y^k\})\in\mathcal X\times\mathcal Y^K$, a real $\tau$ is feasible in (7) together with this decision if and only if $\tau\ge\varphi_\epsilon(x,\{y^k\})$; consequently
--   $$\varphi_\epsilon(x,\{y^k\})=\inf\{\tau\in\mathbb R:\ \tau\ \text{feasible in (7) with}\ (x,\{y^k\})\},$$
--   and the infimum is attained whenever it is finite;
--   2. the optimal values of $(6_\epsilon)$ and (7) coincide.
--
--   The theorem converts the approximate K-adaptability problem, whose objective involves suprema over finitely many polyhedral sets, into a single finite program whose only nonlinearities are products of a binary variable with a continuous one, so that it can be linearized into a mixed-integer linear program.
--
--   **Formalization Note** All values are in the extended reals: the infimum of an empty set of $\tau$ is $+\infty$ (a decision for which some $\Xi_\epsilon(\ell)$, $\ell\in\mathcal L_+$, is nonempty), and it is $-\infty$ when every real $\tau$ is feasible (every $\Xi_\epsilon(\ell)$ is empty). "Equivalent" is pinned down as the per-decision identity above together with equality of optimal values.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 19, Theorem 5, problem (7); proof pp. ec8–ec10 (PDF pp. 42–44)

import Definitions.Def_KAdaptability_Bilinear_Program7

open Matrix

namespace KAdaptability.Bilinear

open Problem

/-- **Theorem 5** (Hanasusanto–Kuhn–Wiesemann, p. 19). The approximate problem (6_ε) is
equivalent to the mixed-integer bilinear program (7). "Equivalent" is pinned down as:
1. for every decision `(x, {y^k}) ∈ 𝒳 × 𝒴^K`, the objective value `φ_ε(x, y)` of (6_ε) equals
   the infimum of the `τ` that are feasible in (7) together with `(x, {y^k})` (in `EReal`,
   `inf ∅ = +∞`), and the feasible `τ` are exactly the reals `τ ≥ φ_ε(x, y)` (so the infimum is
   attained whenever it is finite);
2. the optimal values of (6_ε) and (7) coincide. -/
theorem theorem_5 {N M L nQ R K : ℕ} (P : Problem N M L nQ R) (ε : ℝ) (hε : 0 < ε) :
    (∀ (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ), P.IsDecision x y →
      P.obj6Eps ε x y = P.val7 ε x y ∧
      ∀ τ : ℝ, P.Feasible7 ε x y τ ↔ P.obj6Eps ε x y ≤ (τ : EReal)) ∧
    P.opt6Eps ε K = P.opt7 ε K := by sorry

end KAdaptability.Bilinear
