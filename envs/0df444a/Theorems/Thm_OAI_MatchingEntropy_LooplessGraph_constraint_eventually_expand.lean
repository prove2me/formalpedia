-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_constraint_eventually_expand
-- name    : OAI.MatchingEntropy.LooplessGraph.constraint_eventually_expand
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:18:29.765399+00:00
-- url     : https://prove2.me/theorems/378bb344-f285-4e7d-afe8-78a517ac1384
-- title:
--   Local radial extension inside the degree and odd-cut polytope
-- statement:
--   Let $G$ be a finite loopless multigraph with vertex set $V$ and edge set $E$: every edge $e\in E$ has two distinct endpoints, and parallel edges are allowed (they are distinct elements of $E$). For $x\in\mathbb{R}^E$, a vertex $v$ and a set $S\subseteq V$ write $\deg_x(v)=\sum_{e\ni v}x_e$ for the weighted degree and $x(\delta(S))=\sum_{e\in\delta(S)}x_e$ for the cut mass, where $\delta(S)$ is the set of edges with exactly one endpoint in $S$. The degree and odd-cut polytope is
--
--   $$
--   Q(G)=\Bigl\{x\in\mathbb{R}^E:\ x_e\ge 0\ \text{for all } e,\ \ \deg_x(v)=1\ \text{for all } v,\ \ x(\delta(S))\ge 1\ \text{for all } S\subseteq V \text{ with } |S| \text{ odd}\Bigr\}.
--   $$
--
--   **Theorem.** Let $x\in Q(G)$ and $t>0$. Then there is a neighbourhood $U$ of $x$ in $\mathbb{R}^E$ such that for every $y\in Q(G)\cap U$
--
--   $$
--   x+t^{-1}(y-x)\in Q(G).
--   $$
--
--   In words, every point $y$ of $Q(G)$ close enough to $x$ can be pushed away from $x$ along the ray from $x$ through $y$, by the factor $1/t$, without leaving $Q(G)$. For $t\ge 1$ this already follows from convexity; the content is the case $0<t<1$. It is a polyhedral property, reflecting that $Q(G)$ is cut out by finitely many linear constraints. Combined with Edmonds' identification of $Q(G)$ with the perfect matching polytope (for $|V|$ even), it is the geometric input for the lower semicontinuity of the maximum matching entropy.
--
--   **Formalization Note** The conclusion is an eventual statement for the filter of neighbourhoods of $x$ within $Q(G)$ (`𝓝[G.constraintPolytope] x`), with the scalar written `t⁻¹`. No parity assumption on $|V|$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Face.lean#L262-L300

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

open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem OAI.MatchingEntropy.LooplessGraph.constraint_eventually_expand (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.constraintPolytope] x, x+t⁻¹ • (y-x) ∈ G.constraintPolytope := by sorry
