-- Prove2me | Theorems.Thm_Gomory69_SpecialGroups_vertex_characterization
-- name    : Gomory69.SpecialGroups.vertex_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:13:36.957903+00:00
-- url     : https://prove2.me/theorems/38b605cb-78fd-4756-b839-db874fa43b5c
-- title:
--   p. 506 — vertices of P(G, g0) for groups of exponent s ∈ {2, 3}: independent support, entries below s
-- statement:
--   Let $\mathcal G$ be a finite Abelian group in which every nonzero element has order $s$, where $s = 2$ or $s = 3$ (the groups $\mathcal G_{s^n}$). A nonzero nonnegative integer vector $t$ on $\mathcal G^+$ is a vertex of $P(\mathcal G, g_0)$ for some $g_0 \ne \bar 0$ if and only if the elements $g$ with $t(g) > 0$ are independent and
--   $$t(g) < s \quad\text{for all } g .$$
--
--   This characterization is what the vertex count $v(s^n)$ of pp. 506–507 is built on.
--
--   **Formalization Note** The page does not exclude $t = 0$, whose empty support is independent but which solves no group equation with $g_0 \ne \bar 0$; the hypothesis $t \ne 0$ is added. "Vertex for some $P(\mathcal G, g_0)$" includes that $t$ solves the group equation for that $g_0$.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 506

import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron

namespace Gomory69.SpecialGroups

/-- The vertex characterization of p. 506 (Gomory 1969): if every nonzero element of `𝒢` has order
`s ∈ {2, 3}`, a nonzero nonnegative integer vector `t` is a vertex of `P(𝒢, g₀)` for some
`g₀ ≠ 0̄` if and only if the `g` with `t(g) > 0` are independent and `t(g) < s` for all `g`. -/
theorem vertex_characterization {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ) (hs : s = 2 ∨ s = 3) (hG : AllNonzeroOfOrder G s)
    (t : {g : G // g ≠ 0} → ℕ) (ht : t ≠ 0) :
    (∃ g₀ : G, g₀ ≠ 0 ∧ t ∈ solutionSet g₀ ∧ toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀)) ↔
      (IsIndependent (support t) ∧ ∀ g, t g < s) := by sorry

end Gomory69.SpecialGroups
