-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_matching_covariance_second_variation
-- name    : OAI.MatchingEntropy.matching_covariance_second_variation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:28:24.860806+00:00
-- url     : https://prove2.me/theorems/4f11e8d0-83d0-4fe3-b15d-25cd6e77cd79
-- title:
--   Second-variation inequality for the normalized matching covariance at a maximizer of the entropy defect
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e\in E$ has two distinct endpoints, and parallel edges are allowed. A perfect matching of $G$ is a set $M\subseteq E$ such that every vertex is an endpoint of exactly one edge of $M$; write $\mathcal{M}(G)$ for the finite set of perfect matchings and $\mathbf{1}_M\in\{0,1\}^E$ for the indicator vector of $M$. The perfect matching polytope $P(G)$ is the convex hull of the vectors $\mathbf{1}_M$. For $y\in\mathbb{R}^E$, a feasible law for $y$ is a probability vector $p=(p_M)_{M\in\mathcal{M}(G)}$ with mean $\sum_M p_M\mathbf{1}_M=y$; let $\Pi(G,y)$ be the set of feasible laws, so that $y\in P(G)$ exactly when $\Pi(G,y)$ is nonempty. With the Shannon entropy $H(p)=-\sum_M p_M\log p_M$ (with $0\log 0=0$), the maximum matching entropy at $y$ is
--
--   $$
--   H^*(G,y)=\sup\{H(p):\ p\in\Pi(G,y)\}.
--   $$
--
--   For $y\in\mathbb{R}^E$ let $H(y)=-\sum_{e\in E}y_e\log y_e$ be the entropy of the edge vector itself (not normalized), and for a real parameter $m$ define the entropy defect
--
--   $$
--   D_m(y)=H(y)-8m\bigl(1-e^{-H(y)/m}\bigr)-H^*(G,y).
--   $$
--
--   Let $m>0$, let $x\in\mathbb{R}^E$, let $p\in\Pi(G,x)$ be an entropy maximizer, $H(p)=H^*(G,x)$, and suppose that $x$ maximizes the defect on the polytope: $D_m(y)\le D_m(x)$ for all $y\in P(G)$. Let $E_+=\{e\in E: x_e>0\}$. For each perfect matching $M$ define the normalized centred vector $b_M\in\mathbb{R}^{E_+}$ by
--
--   $$
--   b_M(e)=\frac{\mathbf{1}_M(e)-x_e}{\sqrt{x_e}}\qquad(e\in E_+),
--   $$
--
--   and the normalized matching covariance $C=\sum_{M}p_M\,b_Mb_M^{\top}$, an $E_+\times E_+$ matrix.
--
--   **Theorem.** For every $u\in\mathbb{R}^{E_+}$,
--
--   $$
--   \bigl(8e^{-H(x)/m}-1\bigr)\,\|Cu\|^2+u^{\top}Cu\le 0,
--   $$
--
--   where $\|Cu\|^2=\langle Cu,Cu\rangle$.
--
--   This is exactly the hypothesis of the rank–trace inequality for positive semidefinite matrices with $a=8e^{-H(x)/m}$, which then gives $\operatorname{rank}C\le\bigl(1-8e^{-H(x)/m}\bigr)\operatorname{tr}C$ at a maximizer of the entropy defect. It is the second-order optimality condition of the defect, rewritten in terms of the covariance of the optimal law.
--
--   **Formalization Note** The matrix $C$ is `covariance p (matchingNormalized G x)`, defined as $WW^{\top}$ with $W_{e,M}=\sqrt{p_M}\,b_M(e)$; it is indexed by the subtype `{e // 0 < x e}`, whose cardinality is $|E_+|$. Finiteness of the vertex type is not used. $H(x)$ is `entropy x`, built from `Real.negMulLog`, and $\|Cu\|^2$ is written `(C *ᵥ u) ⬝ᵥ (C *ᵥ u)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean#L203-L243

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
theorem OAI.MatchingEntropy.matching_covariance_second_variation (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x) {m : ℝ} (hm : 0 < m)
    (hmax : ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x)
    (u : {e // 0 < x e} → ℝ) :
    (8*Real.exp (-entropy x/m)-1)*
        ((covariance p (matchingNormalized G x) *ᵥ u) ⬝ᵥ
          (covariance p (matchingNormalized G x) *ᵥ u)) +
      u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) ≤ 0 := by sorry
