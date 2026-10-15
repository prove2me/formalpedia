-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_matching_entropy_dual_bound
-- name    : OAI.MatchingEntropy.matching_entropy_dual_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:03:08.006605+00:00
-- url     : https://prove2.me/theorems/0be8880a-3cb0-43ce-86ec-f93e9f66843b
-- title:
--   Exponential-tilt upper bound for the maximum matching entropy on the optimizer's face
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e$ has two distinct endpoints, and parallel edges are allowed and kept distinct. A *perfect matching* of $G$ is a set $M\subseteq E$ such that every vertex lies on exactly one edge of $M$; write $\mathcal M(G)$ for the finite set of perfect matchings and $\mathbf 1_M\in\mathbb R^E$ for the indicator vector of $M$. A *law* on $\mathcal M(G)$ is a probability vector $p=(p_M)_{M\in\mathcal M(G)}$, that is $p_M\ge0$ and $\sum_M p_M=1$; its *mean* is the edge vector $\operatorname{mean}(p)=\sum_M p_M\mathbf 1_M\in\mathbb R^E$. For $y\in\mathbb R^E$ let $\mathcal F(y)$ be the set of laws with mean $y$, let $H(p)=-\sum_M p_M\log p_M$ (with $0\log 0=0$) be the Shannon entropy, and let $\Phi_G(y)=\sup\{H(p):p\in\mathcal F(y)\}$ be the maximum entropy of a law on perfect matchings with mean $y$. For a weight vector $u\in\mathbb R^E$ and a constant $c\in\mathbb R$, let $a_{u,c}(M)=\sum_{e\in E}u_e\mathbf 1_M(e)-c$ be the corresponding affine score of a matching, and for a law $p$ and a score $a$ let $Z_p(a,t)=\sum_M p_M e^{t\,a(M)}$ be the exponential partition function.
--
--   Let $y\in\mathbb R^E$ and let $p\in\mathcal F(y)$ satisfy $H(p)=\Phi_G(y)$. Let $r$ be a law on $\mathcal M(G)$ supported in the support of $p$ ($r_M=0$ whenever $p_M=0$). Then for all $u\in\mathbb R^E$ and all $c,t\in\mathbb R$,
--
--   $$
--   \Phi_G\big(\operatorname{mean}(r)\big)\;\le\;\log Z_p(a_{u,c},t)\;-\;\sum_{M}r_M\log p_M\;-\;t\sum_{M}r_M\,a_{u,c}(M).
--   $$
--
--   The left side is the true maximum entropy at the mean of $r$, a point of the face spanned by the support of $p$ that may differ from $y$; the right side is an explicit function of $r$ and $t$. In the second-variation argument for the matching entropy bound, $r$ is the score-tilted law $r_M=p_M\big(1+t\,a_{u,c}(M)\big)$, and the inequality then gives an explicit smooth upper bound for $\Phi_G$ along a curve through $y$, with equality at $t=0$; no differentiability of $\Phi_G$ is needed.
--
--   **Formalization Note** $\Phi_G$ is `maxMatchingEntropy G`, defined via `sSup`; $a_{u,c}$ is `linearScore G u c` and $Z_p(a,t)$ is `partition p a t`. Lean's convention $\log0=0$ is harmless here, because $r_M=0$ wherever $p_M=0$. The vertex type is not assumed finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Duality.lean#L101-L130

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem OAI.MatchingEntropy.matching_entropy_dual_bound (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {r : G.Matching → ℝ} (hr : r ∈ probabilitySimplex G.Matching)
    (hrsupport : ∀ M, p M = 0 → r M = 0)
    (u : E → ℝ) (c t : ℝ) :
    maxMatchingEntropy G (G.mean r) ≤
      Real.log (partition p (linearScore G u c) t) - ∑ M, r M * Real.log (p M) -
        t * ∑ M, r M * linearScore G u c M := by sorry
