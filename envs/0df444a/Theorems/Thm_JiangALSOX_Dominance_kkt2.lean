-- Prove2me | Theorems.Thm_JiangALSOX_Dominance_kkt2
-- name    : JiangALSOX.Dominance.kkt2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:07:36.882872+00:00
-- url     : https://prove2.me/theorems/cc4171cc-3d6d-4826-873d-8410e483b2ff
-- title:
--   Appendix A.4 (KKT2): hinge-loss optimality characterization as printed
-- statement:
--   Let $P$ be an arbitrary probability law on $\Xi\subseteq\mathbb R^m$, $g=\max_i g_i$ a positive finite maximum of measurable random losses convex and lower semicontinuous in the decision on a common full-measure set, $X$ nonempty closed and convex inside a closed pointed convex cone, $c\in\mathbb R^n$, and $0<\varepsilon<1$. Assume A1–A2 only. All random relations below hold almost surely.
--
--   For any real budget $t$ and any feasible pair $(x,s)$ of (34), the pair minimizes $E[s]$ over (34) if and only if there exist measurable $\alpha,\mu$ and $\pi\in\mathbb R$ satisfying
--   $$\begin{gathered}
--   -\pi c\in\partial f_\alpha(x)+N_X(x),\quad \mu+\alpha=1,\quad x\in X,\\
--   0\le\alpha\perp(s-g(x,\cdot))\ge0,\quad 0\le\pi\perp(t-c^\top x)\ge0,\quad 0\le\mu\perp s\ge0.
--   \end{gathered}$$
--   Here $f_\alpha(y)=E[\alpha g(y,\cdot)]$. The claim includes the existence of these multipliers for every optimal feasible candidate; no constraint qualification is added. Insight I2 records a boundary-budget instance where this necessity claim fails.
--
--   Differences from the source:
--   - reading: A1–A3 appear in the global preamble, but section 3, Theorem 1 and Appendix A.4 explicitly invoke A1–A2 → A1–A2 only; reason: the three explicit local statements determine the claimed domain
--   - encoding: a measurable random vector on an arbitrary probability space, with a positive number of constraints → its probability law on a subset of finite-dimensional real space and Fin (I+1) constraint indices; reason: taking the law preserves every expectation, probability and almost-sure assertion for functions of that vector; I+1 represents every positive count
--   - encoding: random functions and almost-sure constraints → measurable sections and functional decisions, with one full-measure set for A1; reason: measurability makes the displayed expectations and probabilities meaningful and does not impose a moment condition
--   - encoding: the lower-level expectations and optimality in (34)–(35) → nonnegative extended integrals, feasibility and comparison with every feasible competitor; reason: slacks are bounded below almost surely, so signed primal expectations are always defined, including positive infinity
--   - encoding: the subdifferential of the signed weighted expectation → a finite value at the candidate and supporting inequalities on the domain where the signed expectation is defined; reason: undefined infinity-minus-infinity is represented by none, never by zero; no global integrability assumption is added
--   - encoding: necessary and sufficient KKT conditions for optimality → an iff between optimality and existence of the displayed multipliers for any feasible candidate; reason: both necessity, including certificate existence, and sufficiency are retained
-- source:
--   Nan Jiang and Weijun Xie, ALSO-X and ALSO-X+: Better Convex Approximations for Chance Constrained Programs, arXiv:2012.04763v4 (14 October 2021), https://arxiv.org/abs/2012.04763v4, Appendix A.4, (KKT2), p. 42

import Definitions.Def_JiangALSOX_Dominance_Certificates

namespace JiangALSOX.Dominance

theorem kkt2 {n m I : ℕ} (D : Model n m I) (hD : Assumptions D)
    (t : ℝ) (x : Fin n → ℝ) (s : D.Ξ → ℝ) (hfeas : hingeFeasible D t x s) :
    hingeOptimal D t x s ↔ ∃ α μ π, hingeCertificate D t x s α μ π := by sorry

end JiangALSOX.Dominance
