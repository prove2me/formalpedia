-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_midpoint_law_support
-- name    : OAI.MatchingEntropy.midpoint_law_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:22:49.008923+00:00
-- url     : https://prove2.me/theorems/76e3b37c-54bd-44b4-84bc-ef2b99856de6
-- title:
--   Laws at the endpoints of a segment centred at the marginal are supported inside the entropy optimizer's support
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e\in E$ has two distinct endpoints, and parallel edges are allowed. A perfect matching of $G$ is a set $M\subseteq E$ such that every vertex is an endpoint of exactly one edge of $M$; write $\mathcal{M}(G)$ for the finite set of perfect matchings and $\mathbf{1}_M\in\{0,1\}^E$ for the indicator vector of $M$. The perfect matching polytope $P(G)$ is the convex hull of the vectors $\mathbf{1}_M$. For $y\in\mathbb{R}^E$, a feasible law for $y$ is a probability vector $p=(p_M)_{M\in\mathcal{M}(G)}$ with mean $\sum_M p_M\mathbf{1}_M=y$; let $\Pi(G,y)$ be the set of feasible laws, so that $y\in P(G)$ exactly when $\Pi(G,y)$ is nonempty. With the Shannon entropy $H(p)=-\sum_M p_M\log p_M$ (with $0\log 0=0$), the maximum matching entropy at $y$ is
--
--   $$
--   H^*(G,y)=\sup\{H(p):\ p\in\Pi(G,y)\}.
--   $$
--
--   **Theorem.** Let $x,v\in\mathbb{R}^E$ and $a\in\mathbb{R}$. Suppose $p\in\Pi(G,x)$ is an entropy maximizer, $H(p)=H^*(G,x)$, and $q\in\Pi(G,x+av)$ and $r\in\Pi(G,x-av)$ are feasible laws at the two ends of the segment with midpoint $x$. Then
--
--   $$
--   q_M>0\ \Longrightarrow\ p_M>0\qquad\text{for every } M\in\mathcal{M}(G),
--   $$
--
--   that is, the support of $q$ is contained in the support of $p$. (Applying the theorem with $v$ replaced by $-v$ gives the same conclusion for $r$.)
--
--   An entropy-maximizing law has the largest possible support among the feasible laws at its own mean. This lemma transfers that support property to laws at the endpoints of any segment through $x$ with midpoint $x$. It is used to show that two-sided feasible directions at $x$ are represented by laws living on the support of the optimizer, and hence lie in the span of the optimizer's normalized matching vectors.
--
--   **Formalization Note** Only the edge type is assumed finite; finiteness of the vertex type is not used. The feasible-law sets are `G.feasibleLaws`, and $H^*$ is `maxMatchingEntropy G`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean#L34-L57

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Covariance
import Definitions.Def_OAI_Combinatorics_PerfectMatching_MatchingCovariance

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
open Matrix
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem OAI.MatchingEntropy.midpoint_law_support (G : LooplessGraph V E) {x v : E → ℝ} {a : ℝ}
    {p q r : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hq : q ∈ G.feasibleLaws (x+a • v))
    (hr : r ∈ G.feasibleLaws (x+(-a) • v)) :
    ∀ M, 0 < q M → 0 < p M := by sorry
