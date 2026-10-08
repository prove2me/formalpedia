-- Prove2me | Theorems.Thm_Gomory69_MasterFaces_theorem_7
-- name    : Gomory69.MasterFaces.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:13:09.066887+00:00
-- url     : https://prove2.me/theorems/893a8e17-f92a-47f3-a477-fb38a306b840
-- title:
--   THEOREM 7 — faces as basic feasible solutions of the integer-point system
-- statement:
--   Let $\mathcal N\subseteq\mathcal G\setminus\{0\}$ and $\pi_0>0$. The inequality $\pi\cdot t\ge\pi_0$ defines a face of $P(\mathcal G,\mathcal N,g_0)$ if and only if $\pi$ is a basic feasible solution of the system
--
--   $$\pi\cdot t\ge\pi_0\qquad(t\in T(\mathcal G,\mathcal N,g_0)).$$
--
--   This characterizes Gomory's faces by the rank of the tight integer-point rows. The system can have infinitely many rows, but only $|\mathcal N|$ coefficient variables.
--
--   **Formalization Note.** $\mathcal N$ is assumed nonempty ($n'\ge1$, as on p. 457): for $\mathcal N=\varnothing$ the zero-dimensional coefficient space makes every $\pi$ trivially basic while no nonzero $\pi$, hence no face, exists.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), pp. 469–470, THEOREM 7. DOI: 10.1016/0024-3795(69)90017-2

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_BasicFeasible

namespace Gomory69.MasterFaces

/-- Gomory (1969), THEOREM 7, pp. 469–470. `N` is nonempty (`n′ ≥ 1`, p. 457): at
`N = ∅` the tight-row span is trivially full while no face exists. -/
theorem theorem_7 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : (0 : G) ∉ N) (hNne : N.Nonempty) (g₀ : G) (π : N → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) :
    IsFace N g₀ π π₀ ↔ IsTBasicFeasible N g₀ π₀ π := by sorry

end Gomory69.MasterFaces
