-- Prove2me | Theorems.Thm_Gomory69_SpecialGroups_theorem_2
-- name    : Gomory69.SpecialGroups.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:12:48.291102+00:00
-- url     : https://prove2.me/theorems/1df5b7ab-8d02-4891-92bf-0de5842036ae
-- title:
--   THEOREM 2, p. 460 — every vertex of P(G, g0), g0 ≠ 0, is irreducible
-- statement:
--   Let $\mathcal G$ be a finite Abelian group and $g_0 \ne \bar 0$. Every vertex $x$ of the master polyhedron $P(\mathcal G, g_0)$ is a nonnegative integer solution $t$ of the group equation $\sum_{g \in \mathcal G^+} t(g)\cdot g = g_0$, and that solution is irreducible:
--   $$x \in \operatorname{vert} P(\mathcal G, g_0) \;\Longrightarrow\; x = t \text{ for an irreducible solution } t .$$
--
--   This is the easy half of THEOREM 23: a vertex is irreducible in every finite Abelian group.
--
--   **Formalization Note** The page states THEOREM 2 for $P(\mathcal G, \mathcal N, g_0)$ with any set $\mathcal N$ of nonzero elements; here it is stated for $\mathcal N = \mathcal G^+$, the polyhedron $P(\mathcal G, g_0)$ of §3F. The hypothesis $g_0 \ne \bar 0$ is added: for $g_0 = \bar 0$ the polyhedron $P(\mathcal G, \bar 0)$ excludes $t = 0$ (footnote p. 474), and every nonzero solution $t$ of $\sum t(g) g = \bar 0$ is reducible ($r = 0$, $s = t$), so the statement would fail. That the vertex is an integer solution is part of the conclusion (the page takes it for granted, "$v = (t(g))$").
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 460, THEOREM 2 (for N = G⁺, the polyhedron P(G, g0) of pp. 474–475)

import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron

namespace Gomory69.SpecialGroups

/-- THEOREM 2 (Gomory 1969, p. 460) for the master polyhedron `P(𝒢, g₀)`, `g₀ ≠ 0̄`: every vertex
of `P(𝒢, g₀)` is (the real image of) an irreducible nonnegative integer solution of the group
equation. -/
theorem theorem_2 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (hg₀ : g₀ ≠ 0) (x : {g : G // g ≠ 0} → ℝ)
    (hx : x ∈ Set.extremePoints ℝ (masterPolyhedron g₀)) :
    ∃ t ∈ solutionSet g₀, toReal t = x ∧ IsIrreducible t := by sorry

end Gomory69.SpecialGroups
