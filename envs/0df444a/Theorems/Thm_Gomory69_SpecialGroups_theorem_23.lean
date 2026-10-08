-- Prove2me | Theorems.Thm_Gomory69_SpecialGroups_theorem_23
-- name    : Gomory69.SpecialGroups.theorem_23
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:13:41.669138+00:00
-- url     : https://prove2.me/theorems/d85d22bd-ff8c-4775-b68c-b3cb8bd2de29
-- title:
--   THEOREM 23, p. 505 — in groups of exponent 2 or 3, irreducible solutions are exactly the vertices of P(G, g0)
-- statement:
--   Let $\mathcal G$ be a finite Abelian group in which every nonzero element has order 2, or every nonzero element has order 3, and let $g_0 \ne \bar 0$. Let $t$ be a nonnegative integer solution of the group equation
--   $$\sum_{g \in \mathcal G^+} t(g)\cdot g = g_0 .$$
--   Then
--   1. $t$ is irreducible if and only if $t$ is a vertex of the master polyhedron $P(\mathcal G, g_0)$;
--   2. if $t$ is a vertex, the elements $g$ with $t(g) > 0$ form a set of independent group elements.
--
--   In a general finite Abelian group every vertex is irreducible but many irreducible solutions are not vertices (p. 460); THEOREM 23 identifies the groups $\mathcal G_2, \mathcal G_{2,2}, \ldots$ and $\mathcal G_3, \mathcal G_{3,3}, \ldots$ as those where the two notions coincide, which is what makes the vertices of $P(\mathcal G, g_0)$ countable in closed form for these groups.
--
--   **Formalization Note** The hypothesis "all elements of $\mathcal G$ are of order 2 or all of order 3" is read as "all nonzero elements" (the zero element has order 1), and as one common order $p \in \{2, 3\}$ for all of them: groups with elements of both orders 2 and 3 are not covered. The page states the first sentence without $g_0 \ne \bar 0$ and adds it only for the "Furthermore" clause; it is a hypothesis of the whole statement here, because at $g_0 = \bar 0$ the polyhedron excludes $t = 0$ (footnote p. 474) and every nonzero solution is reducible, so the equivalence fails. The page's gloss "and, hence, part of a group basis" is not formalized; independence is stated as defined on p. 504.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 505, THEOREM 23

import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron

namespace Gomory69.SpecialGroups

/-- THEOREM 23 (Gomory 1969, p. 505): if every nonzero element of `𝒢` has order 2, or every
nonzero element has order 3, and `g₀ ≠ 0̄`, then a solution `t` of the group equation is
irreducible if and only if it is a vertex of `P(𝒢, g₀)`; furthermore, the elements `g` with
`t(g) > 0` in such a vertex form an independent set. -/
theorem theorem_23 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (hg₀ : g₀ ≠ 0) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) :
    (IsIrreducible t ↔ toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀)) ∧
    (toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀) → IsIndependent (support t)) := by sorry

end Gomory69.SpecialGroups
