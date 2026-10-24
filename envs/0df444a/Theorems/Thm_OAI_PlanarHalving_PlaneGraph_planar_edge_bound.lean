-- Prove2me | Theorems.Thm_OAI_PlanarHalving_PlaneGraph_planar_edge_bound
-- name    : OAI.PlanarHalving.PlaneGraph.planar_edge_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:48:42.214638+00:00
-- url     : https://prove2.me/theorems/e9c3bd8e-4779-4db8-a255-fead4bdc605b
-- title:
--   A non-crossing straight-line graph with distinct x-coordinates has at most 3v edges
-- statement:
--   **Statement.** Let $W$ be a finite type and $Q : W \to \mathbb R^2$ (`Point`, from the published bundle `Def_HalvingLines`) be injective with no three distinct points collinear (`orient` nonzero on distinct triples), and with pairwise distinct $x$-coordinates. Let `vertices` be a finite set of points of $W$ and `edges` a finite set of ordered pairs $(u, w)$ such that
--   - every edge goes from left to right: $Q(u)_x < Q(w)_x$;
--   - both endpoints of every edge are in `vertices`;
--   - the open segments of two distinct edges are disjoint (no crossings).
--
--   Then the number of edges is at most $3$ times the number of vertices.
--
--   This is the planar edge bound behind the classical crossing lemma; OpenAI's paper (*A power saving for planar halving lines*) uses it in the proof of Lemma 2.5 in the form "any graph in this drawing satisfies $e' \le 3v' + \mathrm{cr}'$".
--
--   Lean: `OAI.PlanarHalving.PlaneGraph.planar_edge_bound`. In OpenAI's code the result is `Drawing.planar_bound`, stated for a structure `Drawing` (vertices, left-to-right edges with endpoints among the vertices), the predicate `Drawing.NonCrossing` and the predicate `Position` (injective, no three collinear). This statement writes those three out, so that it needs only Mathlib and the published bundle `Def_HalvingLines`; OpenAI's `Drawing.planar_bound` is derived from it in the port.
-- source:
--   OpenAI, A power saving for planar halving lines, OpenAI Math Release, September 25, 2026, Section 2 (proof of Lemma 2.5: "deleting at most one edge for each crossing leaves a simple plane graph"), https://github.com/openai/math (result family 183; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/HalvingLines/PlaneGraph.lean (OpenAI's theorem OAI.PlanarHalving.PlaneGraph.Drawing.planar_bound, with its structures written out)

import Mathlib
import Definitions.Def_HalvingLines

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving
namespace PlaneGraph

variable {V : Type*} [Fintype V] {P : V → Point}

theorem planar_edge_bound {W : Type*} [Fintype W] (Q : W → Point)
    (hQ : Function.Injective Q ∧ ∀ i j l, i ≠ j → j ≠ l → i ≠ l → orient (Q i) (Q j) (Q l) ≠ 0)
    (hx : Function.Injective (fun v => (Q v).1))
    (vertices : Finset W) (edges : Finset (W × W))
    (hright : ∀ e ∈ edges, (Q e.1).1 < (Q e.2).1)
    (hends : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices)
    (hnc : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      Disjoint (openSegment ℝ (Q e.1) (Q e.2)) (openSegment ℝ (Q f.1) (Q f.2))) :
    edges.card ≤ 3 * vertices.card := by
  sorry

end PlaneGraph
end PlanarHalving

end OAI
end
