-- Prove2me | Theorems.Thm_LefebvreVariations_lovasz_hamiltonian_seven_vertices
-- name    : LefebvreVariations.lovasz_hamiltonian_seven_vertices
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:15:22.989141+00:00
-- url     : https://prove2.me/theorems/75f5065c-bed8-415f-9f68-edf9defed778
-- title:
--   Lefebvre's variations, No. 147 — on a theme by Lovász: every connected vertex-transitive graph on 7 vertices has a Hamiltonian path
-- statement:
--   $$G\text{ connected, vertex-transitive on }7\text{ vertices}\ \Longrightarrow\ G\text{ has a Hamiltonian path}.$$
--
--   Lovász's conjecture (1969) says that every finite connected vertex-transitive graph has a Hamiltonian path. On a prime number $p$ of vertices a vertex-transitive graph is a circulant, and it has a Hamiltonian cycle (Turner 1967).
--
--   **Formalization Note** The statement is `lovasz_hamiltonian_conjecture` with `V = Fin 7`: `hconn : G.Connected`, transitivity by automorphisms `φ : Fin 7 ≃ Fin 7` with `φ u = v`, and the conclusion is a `List (Fin 7)` that is `Nodup`, of length `Fintype.card (Fin 7)`, with `List.Chain' G.Adj`.
--
--   **Why this is a variation.** This is a variation of Lovász's Hamiltonian path conjecture (platform problem lovasz_hamiltonian_conjecture, open), in the parent's own formulation with V = Fin 7 fixed. It is a first non-trivial size, a finite statement over graphs on 7 vertices. No formal link to the general conjecture is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   L. Lovász, Problem 11 in Combinatorial Structures and their Applications (Calgary 1969) (cited from memory). J. Turner, 'Point-symmetric graphs with a prime number of points', J. Combin. Theory 3 (1967), 136-145 (cited from memory). Argument checked here: a transitive group of prime degree contains a p-cycle, so G is a circulant on Z/7 and any step of a connected circulant generates Z/7.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Lovász's conjecture for graphs on 7 vertices (a prime number of vertices), parent `lovasz_hamiltonian_conjecture` with `V = Fin 7`: every connected vertex-transitive graph on 7 vertices has a Hamiltonian path. Here such a graph is a circulant, and a Hamiltonian cycle exists (Turner 1967 for any prime number of vertices).
Source: L. Lovász (1969); J. Turner, "Point-symmetric graphs with a prime number of points", J. Combin. Theory 3 (1967), 136-145 (cited from memory). -/
theorem lovasz_hamiltonian_seven_vertices (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (htrans : ∀ u v : Fin 7, ∃ φ : Fin 7 ≃ Fin 7,
      φ u = v ∧ ∀ a b : Fin 7, G.Adj a b ↔ G.Adj (φ a) (φ b)) :
    ∃ path : List (Fin 7), path.Nodup ∧
      path.length = Fintype.card (Fin 7) ∧
      List.Chain' G.Adj path := by
  sorry

end LefebvreVariations
