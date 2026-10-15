-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_matching_optimizer_support
-- name    : OAI.MatchingEntropy.matching_optimizer_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:59:43.406946+00:00
-- url     : https://prove2.me/theorems/bcf2df50-e31e-4760-bfba-9b387072e217
-- title:
--   A maximum-entropy matching law charges every perfect matching charged by a feasible law
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e$ has two endpoints $\ell(e)\neq r(e)$, and parallel edges are distinct elements of $E$. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; $\mathcal M(G)$ denotes the finite set of perfect matchings and $\mathbf 1_M\in\{0,1\}^E$ the indicator vector of $M$. Write $\eta(s)=-s\log s$ (with $\eta(0)=0$) and, for a real vector $z$ indexed by a finite set, $H(z)=\sum_i\eta(z_i)$ for its Shannon entropy. A *feasible law* for $y\in\mathbb{R}^E$ is a probability vector $p=(p_M)_{M\in\mathcal M(G)}$ (so $p_M\ge 0$ and $\sum_M p_M=1$) whose mean is $y$, that is, $\sum_{M}p_M\,\mathbf 1_M(e)=y_e$ for every edge $e$; write $\mathcal F_G(y)$ for the set of feasible laws and $H_{\max}(G,y)=\sup\{H(q):q\in\mathcal F_G(y)\}$ for the maximal entropy of a feasible law.
--
--   **Theorem.** Let $y\in\mathbb{R}^E$ and let $p,q\in\mathcal F_G(y)$ be feasible laws for $y$, where $p$ has maximal entropy, $H(p)=H_{\max}(G,y)$. Then for every perfect matching $M$,
--   $$
--   q_M>0\;\Longrightarrow\;p_M>0 .
--   $$
--
--   Thus a maximum-entropy law with a prescribed edge marginal is supported on every perfect matching that any law with the same marginal can use. Its support is the largest possible, without any assumption that the optimizer has an exponential form. This positivity is what allows logarithms of the optimal probabilities to be differentiated and two-sided perturbations to be made around the optimizer.
--
--   **Formalization Note** $H_{\max}(G,y)$ is `maxMatchingEntropy G y`, defined as the real supremum `sSup` of the entropies of feasible laws. Here the feasible set is nonempty and compact, so this is a genuine attained maximum. The vertex type is not required to be finite in this statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean#L79-L96

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem OAI.MatchingEntropy.matching_optimizer_support (G : LooplessGraph V E) {y : E → ℝ}
    {p q : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hq : q ∈ G.feasibleLaws y) (hopt : entropy p = maxMatchingEntropy G y)
    {M : G.Matching} (hM : 0 < q M) : 0 < p M := by sorry
