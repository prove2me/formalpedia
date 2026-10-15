-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_matching_covariance_rank
-- name    : OAI.MatchingEntropy.matching_covariance_rank
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:27:14.404294+00:00
-- url     : https://prove2.me/theorems/245ed053-fd70-4a55-9a9c-e9eb1ce49be2
-- title:
--   Support size is at most $2|V|$ plus the rank of the normalized matching covariance
-- statement:
--   Let $G$ be a finite loopless multigraph with vertex set $V$ and edge set $E$: every edge $e\in E$ has two distinct endpoints, and parallel edges are allowed (they are distinct elements of $E$). Assume that $|V|$ is even. A perfect matching of $G$ is a set $M\subseteq E$ such that every vertex is an endpoint of exactly one edge of $M$; write $\mathcal{M}(G)$ for the finite set of perfect matchings and $\mathbf{1}_M\in\{0,1\}^E$ for the indicator vector of $M$. The perfect matching polytope $P(G)$ is the convex hull of the vectors $\mathbf{1}_M$. For $y\in\mathbb{R}^E$, a feasible law for $y$ is a probability vector $p=(p_M)_{M\in\mathcal{M}(G)}$ with mean $\sum_M p_M\mathbf{1}_M=y$; let $\Pi(G,y)$ be the set of feasible laws, so that $y\in P(G)$ exactly when $\Pi(G,y)$ is nonempty. With the Shannon entropy $H(p)=-\sum_M p_M\log p_M$ (with $0\log 0=0$), the maximum matching entropy at $y$ is
--
--   $$
--   H^*(G,y)=\sup\{H(p):\ p\in\Pi(G,y)\}.
--   $$
--
--   Let $x\in\mathbb{R}^E$ and let $p\in\Pi(G,x)$ be an entropy maximizer, $H(p)=H^*(G,x)$. Let $E_+=\{e\in E: x_e>0\}$. For each perfect matching $M$ define the normalized centred vector $b_M\in\mathbb{R}^{E_+}$ by
--
--   $$
--   b_M(e)=\frac{\mathbf{1}_M(e)-x_e}{\sqrt{x_e}}\qquad(e\in E_+),
--   $$
--
--   and the normalized matching covariance $C=\sum_{M}p_M\,b_Mb_M^{\top}$, an $E_+\times E_+$ matrix.
--
--   **Theorem.** The number of edges in the support of $x$ satisfies
--
--   $$
--   |E_+|\le 2|V|+\operatorname{rank}C .
--   $$
--
--   For $|V|=2m$ this gives $\operatorname{rank}C\ge |E_+|-4m$: the optimizer's covariance must have large rank when the marginal $x$ is spread over many edges. Together with the exact trace $\operatorname{tr}C=|E_+|-m$ and the second-variation inequality at a maximizer of the entropy defect, this rank bound feeds the rank–trace contradiction behind the bound $H(y)-H^*(G,y)\le 8m\bigl(1-e^{-H(y)/m}\bigr)$.
--
--   **Formalization Note** The matrix $C$ is `covariance p (matchingNormalized G x)`, defined as $WW^{\top}$ with $W_{e,M}=\sqrt{p_M}\,b_M(e)$; it is indexed by the subtype `{e // 0 < x e}`, whose cardinality is $|E_+|$. The rank is `Matrix.rank`, a natural number, and the inequality is in $\mathbb{N}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean#L106-L132

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

theorem OAI.MatchingEntropy.matching_covariance_rank (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x) :
    Fintype.card {e // 0 < x e} ≤ 2*Fintype.card V+
      (covariance p (matchingNormalized G x)).rank := by sorry
