-- Prove2me | Theorems.Thm_Gomory69_MasterFaces_theorem_17
-- name    : Gomory69.MasterFaces.theorem_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:01:08.631736+00:00
-- url     : https://prove2.me/theorems/e4ad4e90-1347-4bd9-a5e3-e690898a05ee
-- title:
--   THEOREM 17 — equalities and subadditivity for master faces
-- statement:
--   Let $g_0\ne0$ and let $\pi\cdot t\ge\pi_0$ be a face of the master polyhedron $P(\mathcal G,g_0)$ with $\pi_0>0$. With $\pi(0)=0$, its coefficients satisfy all three conditions:
--
--   $$\pi(g)+\pi(g_0-g)=\pi_0\quad(g\ne0),$$
--   $$\pi(g)+\pi(h)\ge\pi(g+h)\quad(g,h\ne0),$$
--   $$\pi(g_0)=\pi_0.$$
--
--   These are the face-implied rows of system (13). In the first line, $g=g_0$ uses the zero extension and repeats the last equality.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), pp. 480–481, THEOREM 17 and preceding positive-constant context. DOI: 10.1016/0024-3795(69)90017-2

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.MasterFaces

/-- Gomory (1969), THEOREM 17, pp. 480–481; `π(0) = 0` by extension. -/
theorem theorem_17 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (hg₀ : g₀ ≠ 0) (π : MasterIndex G → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) (hface : IsFace (masterSupport G) g₀ π π₀) :
    (∀ g : MasterIndex G,
      extendZero π (g : G) + extendZero π (g₀ - (g : G)) = π₀) ∧
    (∀ g h : MasterIndex G,
      extendZero π ((g : G) + (h : G)) ≤ π g + π h) ∧
    extendZero π g₀ = π₀ := by sorry

end Gomory69.MasterFaces
