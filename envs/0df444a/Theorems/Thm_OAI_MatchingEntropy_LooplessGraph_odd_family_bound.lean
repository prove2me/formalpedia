-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_odd_family_bound
-- name    : OAI.MatchingEntropy.LooplessGraph.odd_family_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:12:31.784822+00:00
-- url     : https://prove2.me/theorems/f843e937-7eb1-4428-815b-9ac479c47522
-- title:
--   Points of the degree and odd-cut polytope satisfy a fractional Tutte inequality
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$ (parallel edges allowed and kept distinct). For $x\in\mathbb R^E$ let $d_x(v)=\sum_{e\ni v}x_e$ be the weighted degree of $v$, for a finite $S\subseteq V$ let $\delta(S)$ be the set of edges with exactly one endpoint in $S$ and $x(\delta(S))=\sum_{e\in\delta(S)}x_e$, and let $Q(G)$ be the set of $x\ge0$ with $d_x(v)=1$ for every vertex $v$ and $x(\delta(S))\ge1$ for every finite $S\subseteq V$ of odd cardinality.
--
--   Let $x\in Q(G)$, let $U\subseteq V$ be finite, and let $(T_c)_{c\in C}$ be a family of finite vertex sets indexed by a finite set $C$ such that:
--
--   1. every $T_c$ has odd cardinality;
--   2. every $T_c$ is disjoint from $U$;
--   3. the sets $T_c$ are pairwise disjoint;
--   4. no edge of positive weight that avoids $U$ crosses any $T_c$: if $x_e>0$ and neither endpoint of $e$ lies in $U$, then for every $c$ either both endpoints of $e$ lie in $T_c$ or neither does.
--
--   Then
--
--   $$
--   |C|\;\le\;|U| .
--   $$
--
--   Taking for $T_c$ the vertex sets of the odd connected components of the positive-support graph of $x$ after deleting $U$, this is exactly Tutte's condition for that graph. Heuristically, each odd set needs crossing weight at least $1$, all of it must enter through $U$, and the vertices of $U$ have total degree $|U|$.
--
--   **Formalization Note** The vertex type is not assumed finite; the odd-cut condition of $Q(G)$ ranges over all finite vertex sets of odd cardinality. Pairwise disjointness is stated as: if $v\in T_a$ and $v\in T_b$ then $a=b$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Polytope.lean#L47-L134

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

open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq E] in
theorem OAI.MatchingEntropy.LooplessGraph.odd_family_bound (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {C : Type*} [Fintype C] [DecidableEq C]
    (U : Finset V) (T : C → Finset V)
    (hodd : ∀ c, Odd (T c).card)
    (hdisj : ∀ c v, v ∈ T c → v ∉ U)
    (huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b)
    (hclosed : ∀ e, 0 < x e → G.left e ∉ U → G.right e ∉ U →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c) :
    Fintype.card C ≤ U.card := by sorry
