-- Prove2me | Theorems.Thm_OAI_PlanarHalving_PlaneGraph_designated_crossing_bound
-- name    : OAI.PlanarHalving.PlaneGraph.designated_crossing_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:48:58.420286+00:00
-- url     : https://prove2.me/theorems/2d632325-6792-40eb-9d80-0d2e2fdf9ba0
-- title:
--   Crossing lemma with designated endpoints
-- statement:
--   **Statement.** Let $W$ be a finite type and $Q : W \to \mathbb R^2$ (`Point`, published bundle `Def_HalvingLines`) be injective with no three distinct points collinear and with pairwise distinct $x$-coordinates. Let `vertices` ($v$ of them) be a finite set of points of $W$, and `edges` ($e$ of them) a finite set of ordered pairs, each going from left to right ($Q(u)_x < Q(w)_x$) with both endpoints in `vertices`. Let $F \subseteq$ `vertices` be a set of $m$ designated vertices such that every edge has an endpoint in $F$. Let $\mathrm{cr}$ be the number of crossing pairs: unordered pairs of distinct edges whose open segments meet (in Lean, the ordered pairs $(e_1, e_2)$ of edges with $e_1$ before $e_2$ in the enumeration `Fintype.equivFin` and with intersecting open segments, counted with `Set.ncard`). Then
--   $$e^3 \le 2304\, m\, v\, \mathrm{cr} + 13824\, v^3.$$
--
--   This is Lemma 2.5 (Crossings with designated endpoints) of OpenAI's paper (*A power saving for planar halving lines*): "Let a simple graph be drawn with straight segments on $v$ distinct points, with no vertex in an edge interior and no crossings of incident edges. Suppose every edge has an endpoint in a specified set of at most $m \le v$ vertices. If the graph has $e$ edges, then $e^3 \le 2304\, mv\,\mathrm{cr}(G) + 13824\, v^3$." Here no three points are collinear, which gives the paper's two drawing conditions, and the Lean statement in addition asks for distinct $x$-coordinates and left-to-right edges.
--
--   Lean: `OAI.PlanarHalving.PlaneGraph.designated_crossing_bound`. In OpenAI's code the result is `Drawing.designated_crossing`, stated for the structure `Drawing`, the predicate `Position` and the finset `Drawing.crossings`. This statement writes those out, so that it needs only Mathlib and the published bundle `Def_HalvingLines`; OpenAI's `Drawing.designated_crossing` is derived from it in the port.
-- source:
--   OpenAI, A power saving for planar halving lines, OpenAI Math Release, September 25, 2026, Lemma 2.5, https://github.com/openai/math (result family 183; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/HalvingLines/CrossingEstimate.lean (OpenAI's theorem OAI.PlanarHalving.PlaneGraph.Drawing.designated_crossing, with its structures written out)

import Mathlib
import Definitions.Def_HalvingLines

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.PlaneGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] {P : V → Point}

theorem designated_crossing_bound {W : Type*} [Fintype W] (Q : W → Point)
    (hQ : Function.Injective Q ∧ ∀ i j l, i ≠ j → j ≠ l → i ≠ l → orient (Q i) (Q j) (Q l) ≠ 0)
    (hx : Function.Injective (fun v => (Q v).1))
    (vertices : Finset W) (edges : Finset (W × W))
    (hright : ∀ e ∈ edges, (Q e.1).1 < (Q e.2).1)
    (hends : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices)
    (F : Finset W) (hFv : F ⊆ vertices) (hF : ∀ e ∈ edges, e.1 ∈ F ∨ e.2 ∈ F) :
    (edges.card : ℝ) ^ 3 ≤ 2304 * F.card * vertices.card *
      ((↑(edges ×ˢ edges) : Set ((W × W) × (W × W))) ∩
        {ef | Fintype.equivFin (W × W) ef.1 < Fintype.equivFin (W × W) ef.2 ∧
          ¬ Disjoint (openSegment ℝ (Q ef.1.1) (Q ef.1.2)) (openSegment ℝ (Q ef.2.1) (Q ef.2.2))}).ncard + 13824 * (vertices.card : ℝ) ^ 3 := by
  sorry

end PlanarHalving.PlaneGraph

end OAI
end
