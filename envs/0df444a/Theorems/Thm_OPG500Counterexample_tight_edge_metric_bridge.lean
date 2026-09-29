-- Prove2me | Theorems.Thm_OPG500Counterexample_tight_edge_metric_bridge
-- name    : OPG500Counterexample.tight_edge_metric_bridge
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-07T04:07:57.7165+00:00
-- url     : https://prove2.me/theorems/4503a61e-002b-49af-a59d-b8a3dd458134
-- title:
--   Tight-edge metric bridge without unique shortest paths
-- statement:
--   Let $G$ be a finite connected simple graph with a strictly positive real weight on every edge. Every pair of vertices has a globally shortest simple path all of whose edges are tight, where an edge is tight when its one-edge walk is globally shortest between its endpoints.
--
--   Moreover, for every nontight edge $e$, there exist endpoints $x,y$, a globally shortest simple $x$–$y$ path $p$, and a vertex-geodesic simple cycle $C$ satisfying
--
--   $$
--   E(C)=\{e\}\cup E(p).
--   $$
--
--   No uniqueness of shortest paths is assumed.
-- source:
--   Candidate C10, Sections T1 and T2: https://github.com/vibemathing/problem-opg-500-geodesic-cycles/blob/a41fe59b4535851ea55f6e868e938b9aaf81e924/research/artifacts/candidates/opg500-a01-c10/tight-rank.md

import Definitions.Def_opg500_weighted_cycle_models

open Set
open scoped Sym2

namespace OPG500Counterexample

universe u

/-- For a finite connected graph with positive real edge lengths, shortest paths
use tight edges; a nontight edge together with a shortest path between its
endpoints supports a geodesic cycle. No uniqueness of shortest paths is assumed. -/
theorem tight_edge_metric_bridge
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconnected : G.Connected)
    (ℓ : EdgeWeight G) (hpositive : IsPositive ℓ) :
    (∀ x y : V,
      ∃ p : G.Walk x y,
        Walk.IsShortest ℓ p ∧
          ∀ e (he : e ∈ p.edges), Edge.IsTight ℓ ⟨e, p.edges_subset_edgeSet he⟩) ∧
    (∀ e : Edge G, ¬ Edge.IsTight ℓ e →
      ∃ x y : V, ∃ h : G.Adj x y, ∃ p : G.Walk x y, ∃ C : Cycle G,
        e.1 = s(x, y) ∧ Walk.IsShortest ℓ p ∧ C.IsGeodesic ℓ ∧
          C.edgeSet = insert e.1 p.edgeSet) := by sorry

end OPG500Counterexample
