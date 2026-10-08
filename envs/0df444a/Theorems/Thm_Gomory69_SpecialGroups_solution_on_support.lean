-- Prove2me | Theorems.Thm_Gomory69_SpecialGroups_solution_on_support
-- name    : Gomory69.SpecialGroups.solution_on_support
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:13:06.438418+00:00
-- url     : https://prove2.me/theorems/bb1861e4-dc16-4f8c-b081-cd3f6f364565
-- title:
--   p. 506, proof of THEOREM 23 — solutions vanishing off the support of t agree with t modulo p and dominate it
-- statement:
--   Let $\mathcal G$ be a finite Abelian group in which every nonzero element has order $p$, $p \in \{2, 3\}$, and let $t$ be an irreducible nonnegative integer solution of the group equation $\sum_{g} t(g)\cdot g = g_0$. If $u$ is any nonnegative integer solution of the same equation with $u(g) = 0$ whenever $t(g) = 0$, then for every $g \in \mathcal G^+$
--   $$u(g) \equiv t(g) \pmod p \qquad\text{and}\qquad u(g) \ge t(g).$$
--   In particular $t$ is the only such solution whose components are all smaller than $p$.
--
--   **Formalization Note** The page asserts that $t$ is the only solution with components zero outside its support. Literally this fails: in $\mathcal G = \mathbb Z_2$ with $g_0 = 1$, $t = (1)$ is irreducible and $u = (3)$ is another solution with the same support. The page's argument (with $s(g) \equiv t(g) - u(g)$, $0 \le s(g) < p$, and independence of the support) proves $u \equiv t \pmod p$; since an irreducible $t$ has $t(g) < p$, this gives $u \ge t$. The statement records that corrected conclusion.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 506, proof of THEOREM 23 (corrected; see the Formalization Note)

import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron

namespace Gomory69.SpecialGroups

/-- Proof of THEOREM 23 (Gomory 1969, p. 506), corrected: if every nonzero element of `𝒢` has
order `p ∈ {2, 3}` and `t` is an irreducible solution of the group equation, then every solution
`u` vanishing wherever `t` vanishes satisfies `u(g) ≡ t(g) (mod p)` and `u(g) ≥ t(g)` for every
`g`; in particular `t` is the only such solution with all components below `p`. (The page asserts
that `t` is the only such solution outright, which fails, e.g. `𝒢 = ℤ₂`, `t = (1)`, `u = (3)`.) -/
theorem solution_on_support {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) (hirr : IsIrreducible t)
    (u : {g : G // g ≠ 0} → ℕ) (hu : u ∈ solutionSet g₀) (hsupp : ∀ g, t g = 0 → u g = 0) :
    ∀ g, u g ≡ t g [MOD p] ∧ t g ≤ u g := by sorry

end Gomory69.SpecialGroups
