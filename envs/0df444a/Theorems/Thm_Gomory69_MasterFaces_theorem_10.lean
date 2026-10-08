-- Prove2me | Theorems.Thm_Gomory69_MasterFaces_theorem_10
-- name    : Gomory69.MasterFaces.theorem_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:59:02.022527+00:00
-- url     : https://prove2.me/theorems/d387abff-f8a2-4526-a089-e490c2dfd96f
-- title:
--   THEOREM 10 — face coefficients are shortest-path distances
-- statement:
--   Let $\pi\cdot t\ge\pi_0$ be a face of $P(\mathcal G,\mathcal N,g_0)$ with $\pi_0>0$. For any $g\in\mathcal N$, the one-arc path to $g$ has minimum length among all nonnegative integer vectors representing $g$:
--
--   $$\pi(g)\le\sum_{h\in\mathcal N}\pi(h)s(h)\quad\text{whenever }\sum_{h\in\mathcal N}s(h)h=g.$$
--
--   This identifies each facet coefficient with a shortest-path value and supports the following subadditivity consequences.
--
--   **Formalization Note** The unit vector at $g$ attains the bound, so no real infimum or attainment convention is needed.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 473, THEOREM 10. DOI: 10.1016/0024-3795(69)90017-2

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.MasterFaces

/-- Gomory (1969), THEOREM 10, p. 473. -/
theorem theorem_10 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : (0 : G) ∉ N) (g₀ : G) (π : N → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) (hface : IsFace N g₀ π π₀) (g : N) :
    ∀ s : N → ℕ, GroupSolution N (g : G) s → π g ≤ dot π (castSolution s) := by sorry

end Gomory69.MasterFaces
