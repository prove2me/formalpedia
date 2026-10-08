-- Prove2me | Theorems.Thm_Gomory69_SpecialGroups_irreducible_support_independent
-- name    : Gomory69.SpecialGroups.irreducible_support_independent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:12:55.492979+00:00
-- url     : https://prove2.me/theorems/3494ec70-c7b0-477c-93b9-9472d6405887
-- title:
--   p. 506, proof of THEOREM 23 — the support of an irreducible solution is independent
-- statement:
--   Let $\mathcal G$ be a finite Abelian group in which every nonzero element has order $p$, where $p = 2$ or $p = 3$. Let $t$ be an irreducible nonnegative integer solution of the group equation $\sum_{g \in \mathcal G^+} t(g)\cdot g = g_0$, and let $T = \{g : t(g) > 0\}$. Then $T$ is a set of independent group elements: for all integers $(s_g)_{g \in T}$,
--   $$\sum_{g \in T} s_g\, g = \bar 0 \;\Longrightarrow\; s_g\, g = \bar 0 \text{ for all } g \in T .$$
--
--   Combined with THEOREM 2 this gives the "Furthermore" clause of THEOREM 23.
--
--   **Formalization Note** On pp. 505–506 the letter $T$ denotes the support of $t$, not the solution set. The hypothesis that $t$ solves the group equation for some $g_0$ is the page's setting ("Let $t(g)$ be an irreducible solution to the group equation"); no condition on $g_0$ is imposed.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), pp. 505–506, proof of THEOREM 23

import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron

namespace Gomory69.SpecialGroups

/-- Proof of THEOREM 23 (Gomory 1969, pp. 505–506): if every nonzero element of `𝒢` has order
`p ∈ {2, 3}`, then for an irreducible solution `t` of the group equation the elements `g` with
`t(g) > 0` form an independent set. -/
theorem irreducible_support_independent {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) (hirr : IsIrreducible t) :
    IsIndependent (support t) := by sorry

end Gomory69.SpecialGroups
