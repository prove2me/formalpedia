-- Prove2me | Theorems.Thm_LefebvreVariations_graceful_tree_eight_vertices
-- name    : LefebvreVariations.graceful_tree_eight_vertices
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:14:40.233135+00:00
-- url     : https://prove2.me/theorems/f587a4b4-c525-42d6-ba33-9d89fbc9f7aa
-- title:
--   Lefebvre's variations, No. 145 — on a theme by Ringel: every tree on 8 vertices is graceful
-- statement:
--   $$\forall T\text{ tree on }8\text{ vertices}\ \exists f:V(T)\hookrightarrow\{0,\dots,7\}:\ \{|f(u)-f(v)|:uv\in E(T)\}\text{ has }7\text{ distinct values}.$$
--
--   The graceful tree conjecture (Rosa 1967, Ringel--Kotzig) says every tree has a graceful labelling. This is the case of the $23$ trees on $8$ vertices, which have $7$ edges and so use all differences $1,\dots,7$.
--
--   **Formalization Note** The statement is `graceful_tree_conjecture` with `V = Fin 8`: `n := T.edgeFinset.card` and `f : Fin 8 → Fin (n+1)` is injective with `(T.edgeFinset.image (fun e => max (f e.out.1).val (f e.out.2).val - min …)).card = n`.
--
--   **Why this is a variation.** This is a variation of the graceful tree conjecture (platform problem graceful_tree_conjecture, open), in the parent's own formulation with V = Fin 8 fixed: 23 trees, finite and checkable. It is a first non-trivial size beyond paths and stars. No formal link to the general conjecture is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. Rosa (1967); J. A. Gallian, 'A dynamic survey of graph labeling', Electron. J. Combin. DS6 (cited from memory). Computer verification for all trees up to 35 vertices: Aldred and McKay (1998) up to 27 (cited from memory), Fang, 'A computational approach to the graceful tree conjecture', arXiv:1003.3045 (2010), up to 35. All 23 trees on 8 vertices were checked here by exhaustive search.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Graceful tree conjecture (Rosa 1967, Ringel-Kotzig) for the 23 trees on 8 vertices, in the parent's formulation `graceful_tree_conjecture` with `V = Fin 8`: every such tree has an injective labelling of its vertices by `{0,..,7}` whose 7 edge differences are pairwise distinct. Checked by computer on all 23 trees on 8 vertices. Verified by computer for all trees with at most 35 vertices (Aldred and McKay 1998 up to 27; Fang, arXiv:1003.3045, 2010, up to 35).
Source: A. Rosa (1967); J. A. Gallian, "A dynamic survey of graph labeling", Electron. J. Combin., DS6 (cited from memory). -/
theorem graceful_tree_eight_vertices (T : SimpleGraph (Fin 8)) [DecidableRel T.Adj]
    (hT : T.IsTree) :
    let n := T.edgeFinset.card
    ∃ f : Fin 8 → Fin (n + 1),
      Function.Injective f ∧
      (T.edgeFinset.image (fun e =>
        max (f e.out.1).val (f e.out.2).val -
        min (f e.out.1).val (f e.out.2).val)).card = n := by
  sorry

end LefebvreVariations
