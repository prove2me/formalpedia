-- Prove2me | Theorems.Thm_OPG1808_order_eight
-- name    : OPG1808.order_eight
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T01:48:47.214979+00:00
-- url     : https://prove2.me/theorems/11f5f736-7a14-43df-adb3-7cb26fd9237a
-- title:
--   The three-colored tournament theorem through eight vertices
-- statement:
--   Let $T$ be a nonempty tournament on at most eight vertices whose arcs are colored with three colors. Suppose that $T$ has no directed triangle with three pairwise distinct arc colors. Then some vertex reaches every target by a monochromatic directed path:
--
--   $$
--   1\le |V(T)|\le8\quad\text{and no rainbow directed triangle}
--   \quad\Longrightarrow\quad
--   \exists s\in V(T)\ \forall t\in V(T),\ s\leadsto t\text{ monochromatically}.
--   $$
--
--   The path color may depend on the target, unused colors are permitted, and a path of length zero handles the source itself. This is a fully finite supporting bound for the existing order-eleven formalization target; it does not settle the unrestricted conjecture. It formalizes a known finite subcase rather than claiming a new mathematical discovery.
-- source:
--   Finite supporting subcase (at most eight vertices) of OPG1808.order_eleven, https://prove2.me/theorems/a73da177-e54a-4f2b-872f-7a6232e852b8. Obstruction-cycle framework: Georgakopoulos--Sprüssel, On 3-coloured tournaments, https://arxiv.org/abs/0904.1967v2, p. 2, proof of Lemma 2.1. The finite certificate route is separate from that paper; this is not a claim of a new mathematical discovery.

import Definitions.Def_opg1808_colored_tournaments

open OPG1808
universe u

theorem OPG1808.order_eight
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (htournament : IsTournament D)
    (horder : Fintype.card V ≤ 8)
    (hnoRainbow : ¬ HasRainbowDirectedTriangle D color) :
    ∃ s : V, IsMonochromaticSource D color s := by sorry
