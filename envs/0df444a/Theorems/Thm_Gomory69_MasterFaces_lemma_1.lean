-- Prove2me | Theorems.Thm_Gomory69_MasterFaces_lemma_1
-- name    : Gomory69.MasterFaces.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:58:18.061563+00:00
-- url     : https://prove2.me/theorems/1e700783-0795-494a-a06d-e9bd9729595a
-- title:
--   LEMMA 1 — subpaths of a shortest path remain shortest
-- statement:
--   Let $t$ be a shortest path from $0$ to $g_0$, represented by a nonnegative integer vector on $\mathcal N\subseteq\mathcal G\setminus\{0\}$. If $t'\le t$ coordinatewise and $\sum_g t'(g)g=h$, then $t'$ is shortest for its displacement $h$:
--
--   $$\pi\cdot t'\le\pi\cdot s\quad\text{for every }s\in\mathbb N^{\mathcal N}\text{ with }\sum_g s(g)g=h.$$
--
--   Because arc lengths depend only on the increment, this also covers a copy of $t'$ starting at any group vertex.
--
--   **Formalization Note** Paths are multiplicity vectors. The starting vertex of the translated subpath does not change its minimization claim and so is absent from the Lean statement.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 472, LEMMA 1. DOI: 10.1016/0024-3795(69)90017-2

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.MasterFaces

/-- Gomory (1969), LEMMA 1, p. 472; paths are represented by multiplicity vectors. -/
theorem lemma_1 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : (0 : G) ∉ N) (g₀ h : G) (π : N → ℝ)
    (t t' : N → ℕ) (ht : IsShortest N g₀ π t)
    (ht' : GroupSolution N h t') (hle : ∀ g : N, t' g ≤ t g) :
    IsShortest N h π t' := by sorry

end Gomory69.MasterFaces
