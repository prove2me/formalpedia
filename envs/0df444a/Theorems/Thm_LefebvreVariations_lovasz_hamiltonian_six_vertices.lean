-- Prove2me | Theorems.Thm_LefebvreVariations_lovasz_hamiltonian_six_vertices
-- name    : LefebvreVariations.lovasz_hamiltonian_six_vertices
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:14:56.387801+00:00
-- url     : https://prove2.me/theorems/e8908006-63e2-5185-a23a-3c9ef3776916
-- title:
--   Lefebvre's variations, No. 181 — on a theme by Lovász: every connected vertex-transitive graph on 6 vertices has a Hamiltonian path
-- statement:
--   $$G\text{ connected, vertex-transitive on }6\text{ vertices}\ \Longrightarrow\ G\text{ has a Hamiltonian path}.$$
--
--   Lovász's conjecture (1969) says that every finite connected vertex-transitive graph has a Hamiltonian path. All $2^{15}$ labelled graphs on $6$ vertices were enumerated: $146$ are connected and vertex-transitive, and each has a Hamiltonian path.
--
--   **Formalization Note** The statement is `lovasz_hamiltonian_conjecture` with `V = Fin 6`: `hconn : G.Connected`, transitivity by automorphisms `φ : Fin 6 ≃ Fin 6` with `φ u = v`, and the conclusion is a `List (Fin 6)` that is `Nodup`, of length `Fintype.card (Fin 6)`, with `List.Chain' G.Adj`.
--
--   **Why this is a variation.** This is a variation of Lovász's Hamiltonian path conjecture (platform problem lovasz_hamiltonian_conjecture, open), in the parent's own formulation with V = Fin 6 fixed. It is a first non-trivial size, a finite statement over graphs on 6 vertices. No formal link to the general conjecture is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   L. Lovász, Problem 11 in Combinatorial Structures and their Applications (Calgary 1969) (cited from memory). Enumeration done here by computer; known for all vertex-transitive graphs on at most 31 vertices (Royle, McKay and Meringer; cited from memory).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Lovász's conjecture (1969) for graphs on 6 vertices, in the parent's formulation `lovasz_hamiltonian_conjecture` with `V = Fin 6`: every connected vertex-transitive graph on 6 vertices has a Hamiltonian path. Checked by exhaustive enumeration of all 2^15 graphs: 146 labelled graphs are connected and vertex-transitive, and each has a Hamiltonian path. The conjecture is known for all vertex-transitive graphs on at most 31 vertices (Royle, McKay-Meringer) (cited from memory).
Source: L. Lovász, Problem 11, Combinatorial Structures and their Applications (Calgary 1969) (cited from memory). -/
theorem lovasz_hamiltonian_six_vertices (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (htrans : ∀ u v : Fin 6, ∃ φ : Fin 6 ≃ Fin 6,
      φ u = v ∧ ∀ a b : Fin 6, G.Adj a b ↔ G.Adj (φ a) (φ b)) :
    ∃ path : List (Fin 6), path.Nodup ∧
      path.length = Fintype.card (Fin 6) ∧
      List.Chain' G.Adj path := by
  sorry

end LefebvreVariations
