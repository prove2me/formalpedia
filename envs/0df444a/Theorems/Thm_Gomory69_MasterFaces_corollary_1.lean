-- Prove2me | Theorems.Thm_Gomory69_MasterFaces_corollary_1
-- name    : Gomory69.MasterFaces.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:59:28.453645+00:00
-- url     : https://prove2.me/theorems/9a58ca10-3557-4a23-b315-a8af6cb98a62
-- title:
--   COROLLARY 1 — subadditivity of face coefficients
-- statement:
--   Under the face and positive-constant hypotheses of Theorem 10, take $g_1,g_2,g\in\mathcal N$ with $g=g_1+g_2$ in the group. Then
--
--   $$\pi(g)\le\pi(g_1)+\pi(g_2).$$
--
--   These are the subadditive inequalities in the finite system used for the master polyhedron.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 473, COROLLARY 1 following THEOREM 10. DOI: 10.1016/0024-3795(69)90017-2

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.MasterFaces

/-- Gomory (1969), COROLLARY 1, p. 473. -/
theorem corollary_1 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : (0 : G) ∉ N) (g₀ : G) (π : N → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) (hface : IsFace N g₀ π π₀)
    (g₁ g₂ g : N) (hsum : (g : G) = (g₁ : G) + (g₂ : G)) :
    π g ≤ π g₁ + π g₂ := by sorry

end Gomory69.MasterFaces
