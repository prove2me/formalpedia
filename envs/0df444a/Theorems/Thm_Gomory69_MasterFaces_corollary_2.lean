-- Prove2me | Theorems.Thm_Gomory69_MasterFaces_corollary_2
-- name    : Gomory69.MasterFaces.corollary_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:00:55.592116+00:00
-- url     : https://prove2.me/theorems/5896ab8a-43e5-4098-b3c2-9995701a01ee
-- title:
--   COROLLARY 2 — complementary coefficients sum to the face constant
-- statement:
--   Under the face and positive-constant hypotheses of Theorem 10, if $g_1,g_2\in\mathcal N$ and $g_1+g_2=g_0$, then
--
--   $$\pi(g_1)+\pi(g_2)=\pi_0.$$
--
--   This is the complementary equality later applied to every nonzero group element other than $g_0$ in the master polyhedron.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 473, COROLLARY 2 following THEOREM 10. DOI: 10.1016/0024-3795(69)90017-2

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.MasterFaces

/-- Gomory (1969), COROLLARY 2, p. 473. -/
theorem corollary_2 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : (0 : G) ∉ N) (g₀ : G) (π : N → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) (hface : IsFace N g₀ π π₀)
    (g₁ g₂ : N) (hsum : (g₁ : G) + (g₂ : G) = g₀) :
    π g₁ + π g₂ = π₀ := by sorry

end Gomory69.MasterFaces
