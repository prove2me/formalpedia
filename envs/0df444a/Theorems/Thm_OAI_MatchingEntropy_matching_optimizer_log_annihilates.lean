-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_matching_optimizer_log_annihilates
-- name    : OAI.MatchingEntropy.matching_optimizer_log_annihilates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:01:03.386486+00:00
-- url     : https://prove2.me/theorems/652353de-8745-4df8-8a76-b8ad9b8e51ab
-- title:
--   Log-probabilities of a maximum-entropy matching law annihilate every mass- and mean-preserving variation
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e$ has two endpoints $\ell(e)\neq r(e)$, and parallel edges are distinct elements of $E$. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; $\mathcal M(G)$ denotes the finite set of perfect matchings and $\mathbf 1_M\in\{0,1\}^E$ the indicator vector of $M$. Write $\eta(s)=-s\log s$ (with $\eta(0)=0$) and, for a real vector $z$ indexed by a finite set, $H(z)=\sum_i\eta(z_i)$ for its Shannon entropy. A *feasible law* for $y\in\mathbb{R}^E$ is a probability vector $p=(p_M)_{M\in\mathcal M(G)}$ (so $p_M\ge 0$ and $\sum_M p_M=1$) whose mean is $y$, that is, $\sum_{M}p_M\,\mathbf 1_M(e)=y_e$ for every edge $e$; write $\mathcal F_G(y)$ for the set of feasible laws and $H_{\max}(G,y)=\sup\{H(q):q\in\mathcal F_G(y)\}$ for the maximal entropy of a feasible law.
--
--   **Theorem.** Let $y\in\mathbb{R}^E$ and let $p\in\mathcal F_G(y)$ be a feasible law with maximal entropy, $H(p)=H_{\max}(G,y)$. Let $v\in\mathbb{R}^{\mathcal M(G)}$ be a variation that preserves total mass and mean and is supported in the support of $p$:
--   $$
--   \sum_{M}v_M=0,\qquad \sum_{M}v_M\,\mathbf 1_M(e)=0\ \ \text{for every }e\in E,\qquad v_M=0\ \text{whenever }p_M=0 .
--   $$
--   Then
--   $$
--   \sum_{M\in\mathcal M(G)}v_M\log p_M=0 .
--   $$
--
--   This is the first-order (Lagrange) condition for the maximum-entropy problem with prescribed edge marginals, obtained without assuming that the optimizer has an exponential form. By finite-dimensional linear algebra, it says that $(\log p_M)_M$ is orthogonal to every vector supported on $\operatorname{supp}p=\{M:p_M>0\}$ in the kernel of the linear map $v\mapsto\big(\sum_M v_M,\ \operatorname{mean}_G(v)\big)$, where $\operatorname{mean}_G(v)_e=\sum_M v_M\mathbf 1_M(e)$. Equivalently, there are a constant $c$ and edge weights $w\in\mathbb{R}^E$ with $\log p_M=c+\sum_e w_e\mathbf 1_M(e)$ for every $M\in\operatorname{supp}p$.
--
--   **Formalization Note** The mean condition is `G.mean v = 0`, and $H_{\max}(G,y)$ is `maxMatchingEntropy G y`, the real supremum `sSup` of the entropies of feasible laws. Terms with $p_M=0$ vanish on both sides because $v_M=0$ there; Lean's convention $\log 0=0$ is consistent with this. The vertex type is not required to be finite in this statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean#L153-L185

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem OAI.MatchingEntropy.matching_optimizer_log_annihilates (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y) (v : G.Matching → ℝ)
    (hvsum : ∑ M, v M = 0) (hvmean : G.mean v = 0)
    (hsupp : ∀ M, p M = 0 → v M = 0) :
    ∑ M, v M * Real.log (p M) = 0 := by sorry
