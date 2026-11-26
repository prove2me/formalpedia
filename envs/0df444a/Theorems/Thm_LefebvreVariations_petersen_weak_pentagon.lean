-- Prove2me | Theorems.Thm_LefebvreVariations_petersen_weak_pentagon
-- name    : LefebvreVariations.petersen_weak_pentagon
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T23:16:43.625245+00:00
-- url     : https://prove2.me/theorems/5344f911-a609-4298-8e26-e1c88420319c
-- title:
--   Lefebvre's variations, No. 45 — on a theme by Šámal: the Petersen graph has a weak pentagon colouring
-- statement:
--   This is the Petersen case of the weak pentagon problem.
--
--   The Petersen graph is a triangle-free cubic graph and it admits a weak pentagon colouring: its edges can be labelled by five labels, symmetrically in the two endpoints, so that for each label $i$ the edges not labelled $i$ form a bipartite graph.
--
--   An explicit witness uses the five classes of three disjoint edges
--   $\{01,38,79\}$, $\{12,49,58\}$, $\{23,05,69\}$, $\{34,16,57\}$, $\{04,27,68\}$
--   for the standard labelling of the vertices ($0$–$4$ the outer cycle, $5$–$9$ the inner pentagram); removing any one class leaves a bipartite graph, with explicit sides.
--
--   The weak pentagon problem (Šámal) asks whether every triangle-free cubic graph has such a colouring; the Petersen graph, the smallest snark, is the first case where a $3$-edge-colouring shortcut is unavailable.
--
--   **Formalization Note** Triangle-free cubic graphs and weak pentagon colourings are the mission's `OPG434` definitions; the graph is given by its fifteen edges on `Fin 10`.
--
--   **Why this is a variation.** This varies the open weak pentagon problem of Šámal (Open Problem Garden OPG-434, `OPG434`): does every triangle-free cubic graph admit an edge labelling with five labels such that deleting any one label leaves a bipartite graph? It is the first non-bipartite instance, the Petersen graph, which is the smallest snark, so no shortcut from a $3$-edge-colouring is available. It gives an explicit labelling into five classes of three edges for the hardest small test case of the parent conjecture.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   R. Šámal, Weak pentagon problem, Open Problem Garden (OPG-434), as quoted by the platform's OPG-434 statement; the Petersen graph: D. A. Holton and J. Sheehan, The Petersen Graph, Cambridge Univ. Press, 1993. Parent problem: OPG434 weak pentagon conjecture.

import Mathlib
import Definitions.Def_opg434_weak_pentagon

open SimpleGraph

namespace LefebvreVariations

/-- The weak pentagon problem (OPG-434, Šámal): every triangle-free cubic graph has an
edge labelling with five labels such that deleting any one label leaves a bipartite
graph. The first non-bipartite case is the Petersen graph (the smallest snark, so no
three-label shortcut from a 3-edge-colouring exists): it is triangle-free and cubic, and
its fifteen edges split into five triples whose individual removal leaves a bipartite
graph, namely `{01,38,79}, {12,49,58}, {23,05,69}, {34,16,57}, {04,27,68}` (found by exact
cover over the five size-3 bipartizing edge sets of the Petersen graph).
Source: R. Šámal, "Weak pentagon problem", Open Problem Garden (as quoted by OPG-434);
the Petersen graph also maps to the Clebsch graph, which is the target of the stronger
pentagon problem of Nešetřil (see `OPG434.clebsch16_equivalence`). -/
theorem petersen_weak_pentagon :
    OPG434.IsTriangleFreeCubic
        (SimpleGraph.fromEdgeSet
          ({s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(0, 4),
            s(0, 5), s(1, 6), s(2, 7), s(3, 8), s(4, 9),
            s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)} : Set (Sym2 (Fin 10)))) ∧
    OPG434.HasWeakPentagonColoring
        (SimpleGraph.fromEdgeSet
          ({s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(0, 4),
            s(0, 5), s(1, 6), s(2, 7), s(3, 8), s(4, 9),
            s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)} : Set (Sym2 (Fin 10)))) := by
  sorry

end LefebvreVariations
