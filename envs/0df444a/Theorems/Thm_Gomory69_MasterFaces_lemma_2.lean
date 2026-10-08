-- Prove2me | Theorems.Thm_Gomory69_MasterFaces_lemma_2
-- name    : Gomory69.MasterFaces.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:58:42.077322+00:00
-- url     : https://prove2.me/theorems/06c5025c-61a4-4380-965c-a4b0ddbf634e
-- title:
--   LEMMA 2 — every coordinate occurs in a tight shortest path
-- statement:
--   Suppose $\pi\cdot t\ge\pi_0$ is a face of $P(\mathcal G,\mathcal N,g_0)$ with $\pi_0>0$. For every $g\in\mathcal N$ there is a nonnegative integer solution $t$ of the group equation such that
--
--   $$\pi\cdot t=\pi_0,\qquad t(g)>0.$$
--
--   Thus some shortest path to $g_0$ passes through the group vertex $g$. The claim ensures that no coordinate of a facet is absent from all tight integer points.
--
--   **Formalization Note** The displayed integer-vector assertion is the first sentence of the lemma; the path-through-$g$ assertion is its graph interpretation.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), pp. 472–473, LEMMA 2. DOI: 10.1016/0024-3795(69)90017-2

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.MasterFaces

/-- Gomory (1969), LEMMA 2, p. 472. -/
theorem lemma_2 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : (0 : G) ∉ N) (g₀ : G) (π : N → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) (hface : IsFace N g₀ π π₀) (g : N) :
    ∃ t : N → ℕ, GroupSolution N g₀ t ∧
      dot π (castSolution t) = π₀ ∧ 0 < t g := by sorry

end Gomory69.MasterFaces
