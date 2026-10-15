-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_marginal_entropy_support_bound
-- name    : OAI.MatchingEntropy.marginal_entropy_support_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:29:15.530847+00:00
-- url     : https://prove2.me/theorems/a7f67eb6-284d-47ed-bc6d-aa26360daeb4
-- title:
--   Entropy of a perfect matching polytope point is at most $m\log(s/m)$, where $s$ is its support size
-- statement:
--   Let $V$ and $E$ be finite sets. A *loopless multigraph* $G$ with vertex set $V$ and edge set $E$ assigns to each edge $e\in E$ two endpoints $\ell(e),r(e)\in V$ with $\ell(e)\neq r(e)$; distinct edges may have the same endpoints. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* is a set $M\subseteq E$ such that every vertex of $V$ is incident to exactly one edge of $M$. The *perfect matching polytope* $P(G)\subseteq\mathbb{R}^{E}$ is the convex hull of the indicator vectors $\mathbf 1_M\in\{0,1\}^{E}$ of the perfect matchings $M$ of $G$.
--
--   For $x\in\mathbb{R}^{E}$ let
--   $$
--   H(x)=\sum_{e\in E}\eta(x_e),\qquad \eta(u)=-u\log u\quad(\eta(0)=0),
--   $$
--   be its entropy, where $\log$ is the natural logarithm, and let $s=\bigl|\{e\in E: x_e>0\}\bigr|$ be the size of its positive support.
--
--   **Theorem.** Let $m\ge1$ be an integer with $|V|=2m$, and let $x\in P(G)$. Then:
--
--   1. $H(x)\ge0$;
--   2. $s\ge1$, that is, $x$ has at least one positive coordinate;
--   3. the entropy of $x$ is controlled by its support size:
--
--   $$
--   H(x)\;\le\;m\log\frac{s}{m}.
--   $$
--
--   Every point of $P(G)$ has coordinates in $[0,1]$ summing to $m$, because each perfect matching of a graph on $2m$ vertices has exactly $m$ edges. Claim 3 therefore says that such a vector, spread over $s$ positive coordinates, has entropy at most that of the uniform vector with all $s$ entries equal to $m/s$, whose entropy is exactly $m\log(s/m)$. In the proof of the entropy defect bound $H(y)-\mathcal H(y)\le 8m\left(1-e^{-H(y)/m}\right)$ (where $\mathcal H(y)$ is the largest entropy of a law on perfect matchings with mean $y$), it turns a lower bound $H(x)>m\log 8$ on the entropy of an extremal point into the support estimate $s>8m$.
--
--   **Formalization Note** The function $\eta$ is Mathlib's `Real.negMulLog`, the support size is `Fintype.card {e // 0 < x e}` cast to $\mathbb{R}$, and $m$ is a natural number cast to $\mathbb{R}$. The polytope is `convexHull ℝ (Set.range G.indicator)`. Edges form an arbitrary finite type, so parallel edges are allowed. If $G$ has no perfect matching, $P(G)$ is empty and the statement is vacuous.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Main.lean#L49-L82

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

theorem OAI.MatchingEntropy.marginal_entropy_support_bound (G : LooplessGraph V E) {m : ℕ}
    (hm : 0 < m) (hV : Fintype.card V=2*m) {x : E → ℝ} (hx : x ∈ G.polytope) :
    0 ≤ entropy x ∧ 0 < Fintype.card {e // 0 < x e} ∧
      entropy x ≤ (m:ℝ)*Real.log ((Fintype.card {e // 0 < x e}:ℝ)/(m:ℝ)) := by sorry
