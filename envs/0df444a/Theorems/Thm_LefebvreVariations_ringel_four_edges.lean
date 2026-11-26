-- Prove2me | Theorems.Thm_LefebvreVariations_ringel_four_edges
-- name    : LefebvreVariations.ringel_four_edges
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:14:02.518469+00:00
-- url     : https://prove2.me/theorems/4fdf84a8-a3e8-529d-af7b-2f6cf31be79e
-- title:
--   Lefebvre's variations, No. 177 — on a theme by Ringel: Ringel's conjecture holds for every tree with 4 edges
-- statement:
--   $$\forall T \text{ tree on }5\text{ vertices}:\quad K_{9}\ \text{decomposes into } 9\text{ edge-disjoint copies of } T.$$
--
--   Ringel's conjecture (1963) says that $K_{2n+1}$ decomposes into $2n+1$ copies of any tree with $n$ edges. This is the case $n=4$: every tree on $5$ vertices, the complete graph $K_{9}$ splits into $9$ edge-disjoint copies. For these sizes all trees are graceful, and rotating a graceful labelling in $\mathbb Z/9$ gives the decomposition.
--
--   **Formalization Note** The statement is `ringel_conjecture` with `n = 4`: `T : SimpleGraph (Fin (4+1))` is a tree, and there is `decomp : Fin (2*4+1) → Finset (Sym2 (Fin (2*4+1)))` whose parts lie in the edges of `⊤`, cover each edge exactly once, and each contain an injective image of `T`.
--
--   **Why this is a variation.** This is a variation of Ringel's conjecture (platform problem ringel_conjecture, open), in the parent's own formulation with n = 4 fixed, a finite statement over all trees on 5 vertices. A prover can settle it by exhibiting graceful labellings for each of the finitely many trees, so it is the base case of the open problem. No formal link to the general statement is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   G. Ringel (1963); A. Rosa, 'On certain valuations of the vertices of a graph', Theory of Graphs (Internat. Sympos., Rome 1966), 1967: a graceful tree gives a cyclic decomposition (cited from memory). Large n: Montgomery, Pokrovskiy and Sudakov (2021), Keevash and Staden (cited from memory). Verified by computer here for every tree on 5 vertices (each is graceful and the rotations form a decomposition).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Ringel's conjecture (1963) for trees with 4 edges: for every tree `T` on 5 vertices, `K_9` decomposes into 9 edge-disjoint copies of `T`. Same formulation as the platform problem `ringel_conjecture`, with `n = 4` fixed. Verified by computer for every tree on 5 vertices: each is graceful, and the 9 rotations of a graceful labelling inside `Z/9` give the decomposition (Rosa 1967).
Source: G. Ringel, 1963; A. Rosa, "On certain valuations of the vertices of a graph", Theory of Graphs (Rome 1966), 1967; proved for large `n` by Montgomery, Pokrovskiy and Sudakov (2021) and Keevash and Staden (cited from memory). -/
theorem ringel_four_edges (T : SimpleGraph (Fin (4 + 1))) [DecidableRel T.Adj]
    (hT : T.IsTree) :
    ∃ (decomp : Fin (2 * 4 + 1) → Finset (Sym2 (Fin (2 * 4 + 1)))),
      let KN : SimpleGraph (Fin (2 * 4 + 1)) := ⊤
      (∀ i, decomp i ⊆ KN.edgeFinset) ∧
      (∀ e ∈ KN.edgeFinset, ∃! i, e ∈ decomp i) ∧
      ∀ i, ∃ f : Fin (4 + 1) → Fin (2 * 4 + 1),
        Function.Injective f ∧
        ∀ e : Sym2 (Fin (4 + 1)), e ∈ T.edgeFinset →
          Sym2.map f e ∈ decomp i := by
  sorry

end LefebvreVariations
