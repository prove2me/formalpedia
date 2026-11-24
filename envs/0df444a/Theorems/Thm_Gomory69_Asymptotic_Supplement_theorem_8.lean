-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_Supplement_theorem_8
-- name    : Gomory69.Asymptotic.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:23:57.364498+00:00
-- url     : https://prove2.me/theorems/2c535489-99c0-43a6-939d-8902b122f86d
-- title:
--   THEOREM 8 — Zero-constant facets are coordinate hyperplanes
-- statement:
--   Let $G$ be a finite Abelian group, $N\subseteq G\setminus\{0\}$, $g_0\in G$, and let $(\pi,0)$ be a facet of the ordinary corner polyhedron $P(G,N,g_0)$. Then
--   $$\exists h\in N\ \exists a>0:\quad \pi(g)=a\,\mathbf1_{g=h}\quad(g\in N).$$
--   Thus the facet hyperplane is $t(h)=0$. This does not assert that every such coordinate hyperplane is a facet; Theorem 9 gives the criterion.
--
--   The result classifies the zero-constant members of the facet family.
--
--   Differences from the source:
--   - reading: the hyperplanes are represented by unit normals → the given normal is a positive multiple of a coordinate normal; reason: positive rescaling represents the same inequality hyperplane; the proof on p. 471 explicitly obtains a positive coefficient
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 471, THEOREM 8

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.Asymptotic.Supplement

theorem theorem_8 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : 0 ∉ N) (g₀ : G) (π : N → ℝ)
    (hface : Gomory69.MasterFaces.IsFace N g₀ π 0) :
    ∃ h : N, ∃ a : ℝ, 0 < a ∧ π = fun g => if g = h then a else 0 := by sorry

end Gomory69.Asymptotic.Supplement
