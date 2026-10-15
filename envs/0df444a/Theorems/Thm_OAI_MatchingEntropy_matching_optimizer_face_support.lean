-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_matching_optimizer_face_support
-- name    : OAI.MatchingEntropy.matching_optimizer_face_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:02:15.614184+00:00
-- url     : https://prove2.me/theorems/8fb1ffcf-6f84-4228-9fe8-1d525aa410ed
-- title:
--   The support of an entropy-maximizing law on perfect matchings spans a face
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e$ has two distinct endpoints, and parallel edges are allowed and kept distinct. A *perfect matching* of $G$ is a set $M\subseteq E$ such that every vertex lies on exactly one edge of $M$; write $\mathcal M(G)$ for the finite set of perfect matchings and $\mathbf 1_M\in\mathbb R^E$ for the indicator vector of $M$. A *law* on $\mathcal M(G)$ is a probability vector $p=(p_M)_{M\in\mathcal M(G)}$, that is $p_M\ge0$ and $\sum_M p_M=1$; its *mean* is the edge vector $\operatorname{mean}(p)=\sum_M p_M\mathbf 1_M\in\mathbb R^E$. For $y\in\mathbb R^E$ let $\mathcal F(y)$ be the set of laws with mean $y$, let $H(p)=-\sum_M p_M\log p_M$ (with $0\log 0=0$) be the Shannon entropy, and let $\Phi_G(y)=\sup\{H(p):p\in\mathcal F(y)\}$ be the maximum entropy of a law on perfect matchings with mean $y$.
--
--   Let $y\in\mathbb R^E$ and let $p\in\mathcal F(y)$ be an entropy maximizer, $H(p)=\Phi_G(y)$. Let $q$ and $r$ be laws on $\mathcal M(G)$ with equal means, $\operatorname{mean}(q)=\operatorname{mean}(r)$, and assume that $r$ is supported in the support of $p$, i.e. $r_M=0$ whenever $p_M=0$. Then $q$ is supported in the support of $p$ as well:
--
--   $$
--   p_M=0\;\Longrightarrow\;q_M=0\qquad\text{for every }M\in\mathcal M(G).
--   $$
--
--   The means of the laws supported in $\operatorname{supp}p$ form the polytope $F_p=\operatorname{conv}\{\mathbf 1_M:p_M>0\}$, so the theorem says that every law on perfect matchings whose mean lies in $F_p$ charges only matchings that $p$ charges. Consequently $F_p$ is a face of the perfect matching polytope $\operatorname{conv}\{\mathbf 1_M:M\in\mathcal M(G)\}$. This is what allows the maximizer at $y$ to be compared with entropy maximizers at other points of $F_p$ without using a facet description of the polytope.
--
--   **Formalization Note** $\Phi_G(y)$ is `maxMatchingEntropy G y`, defined as the real supremum (`sSup`) of the entropies of the laws in $\mathcal F(y)$; the hypothesis `entropy p = maxMatchingEntropy G y` says that $p$ attains it. The entropy is the sum of Mathlib's `Real.negMulLog`. The vertex type is not assumed finite in the statement (this is automatic as soon as $G$ has a perfect matching, since $E$ is finite).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean#L212-L239

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem OAI.MatchingEntropy.matching_optimizer_face_support (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {q r : G.Matching → ℝ} (hq : q ∈ probabilitySimplex G.Matching)
    (hr : r ∈ probabilitySimplex G.Matching) (hmean : G.mean q = G.mean r)
    (hrsupport : ∀ M, p M = 0 → r M = 0) :
    ∀ M, p M = 0 → q M = 0 := by sorry
