-- Prove2me | Theorems.Thm_Gomory69_SpecialGroups_minimizer_vertex
-- name    : Gomory69.SpecialGroups.minimizer_vertex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:13:26.525671+00:00
-- url     : https://prove2.me/theorems/42d290b3-9cd6-42b0-bbdb-92ba31d92399
-- title:
--   p. 506, proof of THEOREM 23 — an irreducible solution minimizes π and is a vertex
-- statement:
--   Let $\mathcal G$ be a finite Abelian group in which every nonzero element has order $p$, $p \in \{2, 3\}$, and let $t$ be an irreducible nonnegative integer solution of $\sum_{g} t(g)\cdot g = g_0$, with support $T = \{g : t(g) > 0\}$. Define
--   $$\pi(g) = \begin{cases} 0, & g \in T,\\ 1, & g \notin T.\end{cases}$$
--   Then
--   1. $t$ minimizes $\pi\cdot u = \sum_g \pi(g) u(g)$ over the nonnegative integer solutions $u$ of the group equation;
--   2. every minimizing solution $u$ satisfies $u \ge t$ componentwise;
--   3. $t$ is a vertex of $P(\mathcal G, g_0)$.
--
--   This is the step "irreducible $\Rightarrow$ vertex" of THEOREM 23.
--
--   **Formalization Note** The page says that $t$ is the *unique* minimizer of this $\pi$. That fails literally (in $\mathbb Z_2$, $g_0 = 1$: $\pi \equiv 0$ and every solution minimizes), for the reason recorded in the item on solutions vanishing off the support; clause 2 is the corrected form, and clause 3 is the page's conclusion "So $t(g)$ is a vertex".
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 506, proof of THEOREM 23 (corrected; see the Formalization Note)

import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron

namespace Gomory69.SpecialGroups

/-- Proof of THEOREM 23 (Gomory 1969, p. 506), corrected: if every nonzero element of `𝒢` has
order `p ∈ {2, 3}` and `t` is an irreducible solution of the group equation, put `π(g) = 0` where
`t(g) > 0` and `π(g) = 1` where `t(g) = 0`. Then `t` minimizes `π · u` over the solutions `u`,
every minimizer `u` satisfies `u ≥ t` componentwise, and `t` is a vertex of `P(𝒢, g₀)`. -/
theorem minimizer_vertex {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) (hirr : IsIrreducible t) :
    let π : {g : G // g ≠ 0} → ℕ := fun g => if t g = 0 then 1 else 0
    (∀ u ∈ solutionSet g₀, ∑ g, π g * t g ≤ ∑ g, π g * u g) ∧
    (∀ u ∈ solutionSet g₀, ∑ g, π g * u g = ∑ g, π g * t g → t ≤ u) ∧
    toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀) := by sorry

end Gomory69.SpecialGroups
