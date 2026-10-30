-- Prove2me | Theorems.Thm_JiangALSOX_Dominance_theorem_1
-- name    : JiangALSOX.Dominance.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:06:27.918669+00:00
-- url     : https://prove2.me/theorems/f97dde7c-b40e-428e-a32b-aef99a33c855
-- title:
--   Theorem 1: ALSO-X is at least as good as CVaR
-- statement:
--   Let $P$ be an arbitrary probability law on $\Xi\subseteq\mathbb R^m$, $g=\max_i g_i$ a positive finite maximum of measurable random losses convex and lower semicontinuous in the decision on a common full-measure set, $X$ nonempty closed and convex inside a closed pointed convex cone, $c\in\mathbb R^n$, and $0<\varepsilon<1$. Assume A1–A2 only. All random relations below hold almost surely.
--
--   Let $v^A$ be the value of (7): the infimum of budgets admitting a hinge-optimal pair whose slack is zero with probability at least $1-\varepsilon$. Let $v^{CVaR}$ be the value of (13): the infimum of budgets admitting a CVaR-optimal triple with $E[s]-(1-\varepsilon)\beta\le0$. Then
--   $$v^A\le v^{CVaR}.$$
--   Both values are constructed from the original decision data and the complete lower-level argmin sets. The target concerns the exact bilevel formulations, with existential selection among tied minimizers, rather than every tie-breaking implementation of the bisection algorithm. No certificate-existence assumption, uniqueness, Slater condition, A3, finite-support specialization or tolerance appears. The two documented KKT errors are findings about the source's proof, not assumptions or repairs in this target.
--
--   Differences from the source:
--   - reading: A1–A3 appear in the global preamble, but section 3, Theorem 1 and Appendix A.4 explicitly invoke A1–A2 → A1–A2 only; reason: the three explicit local statements determine the claimed domain
--   - encoding: a measurable random vector on an arbitrary probability space, with a positive number of constraints → its probability law on a subset of finite-dimensional real space and Fin (I+1) constraint indices; reason: taking the law preserves every expectation, probability and almost-sure assertion for functions of that vector; I+1 represents every positive count
--   - encoding: random functions and almost-sure constraints → measurable sections and functional decisions, with one full-measure set for A1; reason: measurability makes the displayed expectations and probabilities meaningful and does not impose a moment condition
--   - encoding: optimal values written as minima → EReal infima of the original feasible budget sets; reason: this agrees with every finite attained value and assigns positive infinity to the empty set and negative infinity to an unbounded-below set, without assuming attainment
--   - encoding: E[s] and E[s]-(1-epsilon) beta in the lower-level objectives → positive extended expectation and epsilon beta plus the positive expectation of s-beta; reason: the feasibility constraints give s nonnegative or bounded below by beta almost surely, so the formulas agree even at positive infinity
--   - reading: the pair or triple in (7b) or (13b) is an optimization variable → existential membership in the full lower-level argmin set; reason: this is the literal optimistic bilevel formulation; the source separately discusses unlucky algorithmic choices in Appendix C
-- source:
--   Nan Jiang and Weijun Xie, ALSO-X and ALSO-X+: Better Convex Approximations for Chance Constrained Programs, arXiv:2012.04763v4 (14 October 2021), https://arxiv.org/abs/2012.04763v4, Theorem 1, p. 13; Appendix A.4, pp. 41–43

import Definitions.Def_JiangALSOX_Dominance_Programs

namespace JiangALSOX.Dominance

theorem theorem_1 {n m I : ℕ} (D : Model n m I) (hD : Assumptions D) :
    alsoValue D ≤ cvarValue D := by sorry

end JiangALSOX.Dominance
