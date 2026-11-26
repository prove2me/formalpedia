-- Prove2me | Theorems.Thm_LefebvreVariations_ringel_five_edges
-- name    : LefebvreVariations.ringel_five_edges
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:14:19.081357+00:00
-- url     : https://prove2.me/theorems/4b897629-9a54-462c-8661-264008e21692
-- title:
--   Lefebvre's variations, No. 144 — on a theme by Ringel: Ringel's conjecture holds for every tree with 5 edges
-- statement:
--   $$\forall T \text{ tree on }6\text{ vertices}:\quad K_{11}\ \text{decomposes into } 11\text{ edge-disjoint copies of } T.$$
--
--   Ringel's conjecture (1963) says that $K_{2n+1}$ decomposes into $2n+1$ copies of any tree with $n$ edges. This is the case $n=5$: every tree on $6$ vertices, the complete graph $K_{11}$ splits into $11$ edge-disjoint copies. For these sizes all trees are graceful, and rotating a graceful labelling in $\mathbb Z/11$ gives the decomposition.
--
--   **Formalization Note** The statement is `ringel_conjecture` with `n = 5`: `T : SimpleGraph (Fin (5+1))` is a tree, and there is `decomp : Fin (2*5+1) → Finset (Sym2 (Fin (2*5+1)))` whose parts lie in the edges of `⊤`, cover each edge exactly once, and each contain an injective image of `T`.
--
--   **Why this is a variation.** This is a variation of Ringel's conjecture (platform problem ringel_conjecture, open), in the parent's own formulation with n = 5 fixed, a finite statement over all trees on 6 vertices. A prover can settle it by exhibiting graceful labellings for each of the finitely many trees, so it is the base case of the open problem. No formal link to the general statement is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   G. Ringel (1963); A. Rosa, 'On certain valuations of the vertices of a graph', Theory of Graphs (Internat. Sympos., Rome 1966), 1967: a graceful tree gives a cyclic decomposition (cited from memory). Large n: Montgomery, Pokrovskiy and Sudakov (2021), Keevash and Staden (cited from memory). Verified by computer here for every tree on 6 vertices (each is graceful and the rotations form a decomposition).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Ringel's conjecture (1963) for trees with 5 edges: for every tree `T` on 6 vertices, `K_11` decomposes into 11 edge-disjoint copies of `T`. Same formulation as the platform problem `ringel_conjecture`, with `n = 5` fixed. Verified by computer for every tree on 6 vertices: each is graceful, and the 11 rotations of a graceful labelling inside `Z/11` give the decomposition (Rosa 1967).
Source: G. Ringel, 1963; A. Rosa, "On certain valuations of the vertices of a graph", Theory of Graphs (Rome 1966), 1967; proved for large `n` by Montgomery, Pokrovskiy and Sudakov (2021) and Keevash and Staden (cited from memory). -/
theorem ringel_five_edges (T : SimpleGraph (Fin (5 + 1))) [DecidableRel T.Adj]
    (hT : T.IsTree) :
    ∃ (decomp : Fin (2 * 5 + 1) → Finset (Sym2 (Fin (2 * 5 + 1)))),
      let KN : SimpleGraph (Fin (2 * 5 + 1)) := ⊤
      (∀ i, decomp i ⊆ KN.edgeFinset) ∧
      (∀ e ∈ KN.edgeFinset, ∃! i, e ∈ decomp i) ∧
      ∀ i, ∃ f : Fin (5 + 1) → Fin (2 * 5 + 1),
        Function.Injective f ∧
        ∀ e : Sym2 (Fin (5 + 1)), e ∈ T.edgeFinset →
          Sym2.map f e ∈ decomp i := by
  sorry

end LefebvreVariations
