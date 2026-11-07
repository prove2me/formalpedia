-- Prove2me | Theorems.Thm_MonoTestDAG_distance_via_violation_graph
-- name    : MonoTestDAG.distance_via_violation_graph
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:09:24.000193+00:00
-- url     : https://prove2.me/theorems/6a964225-e013-45e6-9ed5-97fd2633b3f1
-- title:
--   §2.3 — $d_{\mathrm{mon}}(f)$ equals the maximum matching and the minimum vertex cover of the violation graph
-- statement:
--   Let $G=(V,E)$ be a DAG and $f:V\to\mathbb R$. The violation graph $G_f$ is bipartite, with left part $V_L$ and right part $V_R$ (two copies of $V$), and an edge $\{u_L,v_R\}$ whenever $u\leadsto v$ and $f(u)>f(v)$. Then:
--
--   1. a set $S\subseteq V$ can be left unchanged by a monotone correction if and only if it is an antichain of the violation relation $\prec_f$;
--   2. $d_{\mathrm{mon}}(f)$ is the maximum size of a matching of $G_f$;
--   3. $d_{\mathrm{mon}}(f)$ is the minimum size $|K_L|+|K_R|$ of a vertex cover of $G_f$.
--
--   This characterization is the bridge between distance and combinatorics: an $\varepsilon$-far function has more than $\varepsilon n$ disjoint comparable violating pairs.
--
--   Differences from the source:
--   - encoding: the bipartite graph G_f on two copies of V → the relation `Violates E f` on V × V, with the published `IsMatching` and `IsVertexCover`; reason: pairs (u, v) are the edges {u_L, v_R}
--   - encoding: "equals the maximum matching size" and "the minimum vertex cover size" → attained, and a bound for every matching / every cover; reason: the definition of maximum and minimum
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §2.3, p.11 (citing [16, 19])

import Mathlib
import Definitions.Def_MonoTestDAG_dmon
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching

namespace MonoTestDAG

open OAI.SeymourSecondNeighborhood.Bipartite

/-- **Distance to monotonicity via the violation graph** ([16, 19], recalled in §2.3).
Let `G = (V, E)` be a DAG and `f : V → ℝ`. The violation graph `G_f` is bipartite with left part
`V_L` and right part `V_R` (two copies of `V`) and an edge `{u_L, v_R}` whenever `u ⇝ v` and
`f(u) > f(v)`. Then
1. a set `S ⊆ V` can be left unchanged by a monotone correction iff it is an antichain of the
   violation order `u ≺_f v :⟺ u ⇝ v ∧ f(u) > f(v)`;
2. `d_mon(f)` is the maximum size of a matching of `G_f` (attained, and an upper bound for every
   matching);
3. `d_mon(f)` is the minimum size `|K_L| + |K_R|` of a vertex cover of `G_f` (attained, and a lower
   bound for every vertex cover).

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §2.3, p.11 (citing [16, 19]).

**Formalization Note.** The edges of `G_f` are the pairs `(u, v)` with `Violates E f u v`; matchings
and vertex covers are the published `OAI.SeymourSecondNeighborhood.Bipartite.IsMatching` and
`IsVertexCover` on this bipartite relation. -/
theorem distance_via_violation_graph {V : Type} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) (hE : IsDAG E) (f : V → ℝ) :
    (∀ S : Finset V, (∃ g : V → ℝ, IsMonotone E g ∧ ∀ v ∈ S, g v = f v) ↔
        ∀ u ∈ S, ∀ v ∈ S, ¬ Violates E f u v) ∧
    (∃ M : Finset (V × V), IsMatching (Violates E f) M ∧ M.card = dmon E f) ∧
    (∀ M : Finset (V × V), IsMatching (Violates E f) M → M.card ≤ dmon E f) ∧
    (∃ KL KR : Finset V, IsVertexCover (Violates E f) KL KR ∧ KL.card + KR.card = dmon E f) ∧
    (∀ KL KR : Finset V, IsVertexCover (Violates E f) KL KR → dmon E f ≤ KL.card + KR.card) := by sorry

end MonoTestDAG
