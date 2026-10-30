-- Prove2me | Theorems.Thm_JiangALSOX_Dominance_kkt1
-- name    : JiangALSOX.Dominance.kkt1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:07:23.481202+00:00
-- url     : https://prove2.me/theorems/9202da67-4726-48cf-98eb-885c3ccdbf5d
-- title:
--   Appendix A.4 (KKT1): CVaR optimality characterization as printed
-- statement:
--   Let $P$ be an arbitrary probability law on $\Xi\subseteq\mathbb R^m$, $g=\max_i g_i$ a positive finite maximum of measurable random losses convex and lower semicontinuous in the decision on a common full-measure set, $X$ nonempty closed and convex inside a closed pointed convex cone, $c\in\mathbb R^n$, and $0<\varepsilon<1$. Assume A1–A2 only. All random relations below hold almost surely.
--
--   For any real budget $t$ and any feasible triple $(x,s,\beta)$ of (35), the triple minimizes $E[s]-(1-\varepsilon)\beta$ over (35) if and only if there exist measurable $\alpha,\mu$ and $\pi\in\mathbb R$ satisfying
--   $$\begin{gathered}
--   -\pi c\in\partial f_\alpha(x)+N_X(x),\quad E[\mu]\le1-\varepsilon,\quad\mu+\alpha=1,\\
--   0\le\alpha\perp(s-g(x,\cdot))\ge0,\quad 0\le\pi\perp(t-c^\top x)\ge0,\\
--   0\le\mu\perp(s-\beta)\ge0,\quad\beta\le0,\quad x\in X.
--   \end{gathered}$$
--   Here $f_\alpha(y)=E[\alpha g(y,\cdot)]$ and $N_X$ and $\partial$ have the conventions given in the definition items. The printed claim is retained, including its false sufficiency: insight I1 records the missing beta complementarity and a concrete counterexample. No corrected system is substituted.
--
--   Differences from the source:
--   - reading: A1–A3 appear in the global preamble, but section 3, Theorem 1 and Appendix A.4 explicitly invoke A1–A2 → A1–A2 only; reason: the three explicit local statements determine the claimed domain
--   - encoding: a measurable random vector on an arbitrary probability space, with a positive number of constraints → its probability law on a subset of finite-dimensional real space and Fin (I+1) constraint indices; reason: taking the law preserves every expectation, probability and almost-sure assertion for functions of that vector; I+1 represents every positive count
--   - encoding: random functions and almost-sure constraints → measurable sections and functional decisions, with one full-measure set for A1; reason: measurability makes the displayed expectations and probabilities meaningful and does not impose a moment condition
--   - encoding: the lower-level expectations and optimality in (34)–(35) → nonnegative extended integrals, feasibility and comparison with every feasible competitor; reason: slacks are bounded below almost surely, so signed primal expectations are always defined, including positive infinity
--   - encoding: the subdifferential of the signed weighted expectation → a finite value at the candidate and supporting inequalities on the domain where the signed expectation is defined; reason: undefined infinity-minus-infinity is represented by none, never by zero; no global integrability assumption is added
--   - encoding: necessary and sufficient KKT conditions for optimality → an iff between optimality and existence of the displayed multipliers for any feasible candidate; reason: both necessity, including certificate existence, and sufficiency are retained
-- source:
--   Nan Jiang and Weijun Xie, ALSO-X and ALSO-X+: Better Convex Approximations for Chance Constrained Programs, arXiv:2012.04763v4 (14 October 2021), https://arxiv.org/abs/2012.04763v4, Appendix A.4, (KKT1), p. 42

import Definitions.Def_JiangALSOX_Dominance_Certificates

namespace JiangALSOX.Dominance

theorem kkt1 {n m I : ℕ} (D : Model n m I) (hD : Assumptions D)
    (t : ℝ) (x : Fin n → ℝ) (s : D.Ξ → ℝ) (β : ℝ)
    (hfeas : cvarFeasible D t x s β) :
    cvarOptimal D t x s β ↔ ∃ α μ π, cvarCertificate D t x s β α μ π := by sorry

end JiangALSOX.Dominance
