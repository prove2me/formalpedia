-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_theorem_2
-- name    : Gomory69.Asymptotic.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:57:44.72214+00:00
-- url     : https://prove2.me/theorems/8b049dc7-84f1-4250-9005-1597ae648b80
-- title:
--   THEOREM 2, p. 460 — every vertex of P(G, N, g0) is irreducible
-- statement:
--   Let $\mathcal G$ be a finite Abelian group, $\mathcal N$ a set of nonzero elements of $\mathcal G$ and $g_0\in\mathcal G$. Every vertex $v$ of $P(\mathcal G,\mathcal N,g_0)$ is an integer point: there is a nonnegative integer solution $t$ of the group equation
--
--   $$\sum_{g\in\mathcal N}t(g)\cdot g=g_0$$
--
--   with $v=t$ (coordinatewise), and this $t$ is irreducible.
--
--   Together with THEOREM 1, this bounds the size of every vertex of the corner polyhedron.
--
--   **Formalization Note** "Vertex" is an extreme point of the convex hull. The paper's one-line statement contains two facts, made explicit here: a vertex of $P(\mathcal G,\mathcal N,g_0)$ is one of the integer solutions it is the hull of, and that integer solution is irreducible.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 460, THEOREM 2

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron

namespace Gomory69.Asymptotic

/-- THEOREM 2 (p. 460): every vertex of `P(𝒢, 𝒩, g₀)` is (the real image of) an
irreducible nonnegative integer solution of the group equation (5). -/
theorem theorem_2 {G : Type*} [AddCommGroup G] [Finite G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (g₀ : G) (v : ↥𝒩 → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (groupPolyhedron 𝒩 g₀)) :
    ∃ t ∈ groupSolutions 𝒩 g₀, toReal 𝒩 t = v ∧ IsIrreducible 𝒩 t := by sorry

end Gomory69.Asymptotic
