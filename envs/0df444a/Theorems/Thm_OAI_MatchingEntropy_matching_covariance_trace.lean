-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_matching_covariance_trace
-- name    : OAI.MatchingEntropy.matching_covariance_trace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:27:52.503802+00:00
-- url     : https://prove2.me/theorems/12b92f95-2f21-4b19-8290-ea3c8471a2f7
-- title:
--   Trace of the normalized matching covariance equals $|E_+|-m$
-- statement:
--   Let $G$ be a finite loopless multigraph with vertex set $V$ and edge set $E$: every edge $e\in E$ has two distinct endpoints, and parallel edges are allowed (they are distinct elements of $E$). Let $m$ be a natural number with $|V|=2m$. A perfect matching of $G$ is a set $M\subseteq E$ such that every vertex is an endpoint of exactly one edge of $M$; write $\mathcal{M}(G)$ for the finite set of perfect matchings and $\mathbf{1}_M\in\{0,1\}^E$ for the indicator vector of $M$. The perfect matching polytope $P(G)$ is the convex hull of the vectors $\mathbf{1}_M$. For $y\in\mathbb{R}^E$, a feasible law for $y$ is a probability vector $p=(p_M)_{M\in\mathcal{M}(G)}$ with mean $\sum_M p_M\mathbf{1}_M=y$; let $\Pi(G,y)$ be the set of feasible laws, so that $y\in P(G)$ exactly when $\Pi(G,y)$ is nonempty.
--
--   Let $x\in\mathbb{R}^E$ and let $p\in\Pi(G,x)$ be any feasible law (optimality is not required). Let $E_+=\{e\in E: x_e>0\}$. For each perfect matching $M$ define the normalized centred vector $b_M\in\mathbb{R}^{E_+}$ by
--
--   $$
--   b_M(e)=\frac{\mathbf{1}_M(e)-x_e}{\sqrt{x_e}}\qquad(e\in E_+),
--   $$
--
--   and the normalized matching covariance $C=\sum_{M}p_M\,b_Mb_M^{\top}$, an $E_+\times E_+$ matrix.
--
--   **Theorem.**
--
--   $$
--   \operatorname{tr}C=|E_+|-m .
--   $$
--
--   Each diagonal entry $C_{ee}$ is the variance of the normalized indicator $(\mathbf{1}_M(e)-x_e)/\sqrt{x_e}$ under $p$, which equals $1-x_e$; the trace is therefore the support size minus the total edge mass $\sum_e x_e=m$ of a point of the perfect matching polytope. In the matching-entropy argument this exact trace is combined with the rank lower bound $\operatorname{rank}C\ge|E_+|-4m$ and the rank–trace inequality coming from the second variation.
--
--   **Formalization Note** The matrix $C$ is `covariance p (matchingNormalized G x)`, defined as $WW^{\top}$ with $W_{e,M}=\sqrt{p_M}\,b_M(e)$; it is indexed by the subtype `{e // 0 < x e}`, whose cardinality is $|E_+|$. The identity is an equality of real numbers, with $|E_+|$ and $m$ cast to $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean#L186-L201

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

theorem OAI.MatchingEntropy.matching_covariance_trace (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) {m : ℕ}
    (hV : Fintype.card V=2*m) :
    (covariance p (matchingNormalized G x)).trace = Fintype.card {e // 0 < x e}-(m:ℝ) := by sorry
