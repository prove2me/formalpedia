-- Prove2me | Theorems.Thm_LefebvreVariations_two_color_of_two_degenerate
-- name    : LefebvreVariations.two_color_of_two_degenerate
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:20:27.745585+00:00
-- url     : https://prove2.me/theorems/60d69216-79ba-4d07-9005-5a71af1ee82f
-- title:
--   Lefebvre's variations, No. 16 — on a theme by Neumann-Lara: acyclic two-colourings of orientations of 2-degenerate planar graphs
-- statement:
--   This is the two-colour conjecture for planar digraphs in the $2$-degenerate case.
--
--   Let $G$ be a finite planar graph in which every nonempty set $S$ of vertices contains a vertex with at most two neighbours in $S$ (equivalently, $G$ is $2$-degenerate: outerplanar graphs, series–parallel graphs and planar graphs of girth at least $6$ all qualify). Let $D$ be any orientation of $G$. Then the vertices of $D$ can be coloured with two colours so that
--
--   $$
--   \text{no directed cycle of } D \text{ is monochromatic}.
--   $$
--
--   Neumann-Lara conjectured that every orientation of a planar graph admits such a $2$-colouring (dichromatic number at most $2$). In the $2$-degenerate case the colouring is built greedily: a vertex with at most two neighbours can take a colour used by at most one of them, and then it cannot lie on a monochromatic directed cycle, which would need both an in-neighbour and an out-neighbour of its colour.
--
--   **Formalization Note** The digraph, orientation, planarity and acyclic $2$-colouring are the mission's `OPG169` definitions; planarity is kept as a hypothesis although the argument does not use it.
--
--   **Why this is a variation.** This varies the Neumann-Lara conjecture on two acyclic colours for orientations of planar graphs (`OPG169.root_problem`, Open Problem Garden), which says every orientation of a planar graph has dichromatic number at most $2$. It is the special case of $2$-degenerate planar graphs, which include outerplanar graphs, series-parallel graphs and planar graphs of girth at least $6$. Settling it removes this large class from the parent, leaving the planar graphs of larger degeneracy.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Conjecture: V. Neumann-Lara, The dichromatic number of a digraph, J. Combin. Theory Ser. B 33 (1982), 265–270 (every orientation of a planar graph has dichromatic number at most 2). The 2-degenerate case follows from the standard greedy argument for degenerate digraphs; see also D. Bokal, G. Fijavž, M. Juvan, P. M. Kayll and B. Mohar, The circular chromatic number of a digraph, J. Graph Theory 46 (2004), 227–240. Parent problem: OPG169.root_problem (Open Problem Garden: two acyclic colours for planar orientations).

import Definitions.Def_opg169_planar_dichromatic

set_option autoImplicit false

namespace LefebvreVariations

universe u

/-- **The Two Color Conjecture for 2-degenerate planar graphs** (greedy bound of Neumann-Lara,
*J. Combin. Theory Ser. B* 33 (1982) 265–270: a `d`-degenerate underlying graph gives dichromatic
number at most `⌊d/2⌋ + 1`; see Bokal–Fijavž–Juvan–Kayll–Mohar, *J. Graph Theory* 46 (2004)
227–240). `G` is 2-degenerate: every nonempty finite vertex set has a vertex with at most two
neighbours inside it (outerplanar graphs, series-parallel graphs, planar graphs of girth `≥ 6`). -/
theorem two_color_of_two_degenerate {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : OPG169.Digraph V) (hplanar : OPG169.IsPlanar G) (horientation : OPG169.IsOrientationOf D G)
    (hdeg : ∀ S : Finset V, S.Nonempty →
      ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 2) :
    OPG169.HasAcyclicTwoColoring D := by
  sorry

end LefebvreVariations
