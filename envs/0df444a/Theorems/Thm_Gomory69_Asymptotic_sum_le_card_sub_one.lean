-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_sum_le_card_sub_one
-- name    : Gomory69.Asymptotic.sum_le_card_sub_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:57:45.433894+00:00
-- url     : https://prove2.me/theorems/14451dc6-2716-46ca-9b17-0d64cb3e40fa
-- title:
--   Proof of THEOREM 4, p. 462 — an irreducible t has Σ t(g) ≤ |G| − 1
-- statement:
--   Let $\mathcal G$ be a finite Abelian group and $\mathcal N$ a set of nonzero elements of $\mathcal G$. If the nonnegative integer vector $t$ is irreducible, then
--
--   $$\sum_{g\in\mathcal N}t(g)\le|\mathcal G|-1.$$
--
--   This is the first step of the proof of THEOREM 4, applied there to a minimizing vertex $t^*$.
--
--   **Formalization Note** The page writes "$\sum_{g\in\mathcal N}(1+t^*(g))\le|\mathcal G|=D$. Expanding shows ..."; the inequality it expands is THEOREM 1's product $\prod(1+t^*(g))\le|\mathcal G|$, and the sum is a printing slip. The subtraction is in $\mathbb N$, which is exact because $|\mathcal G|\ge 1$.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 462, proof of THEOREM 4

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron

namespace Gomory69.Asymptotic

/-- Proof of THEOREM 4 (p. 462), first step: an irreducible nonnegative integer vector `t`
satisfies `∑_{g ∈ 𝒩} t(g) ≤ |𝒢| − 1` (natural-number subtraction is exact here, as
`|𝒢| ≥ 1`). -/
theorem sum_le_card_sub_one {G : Type*} [AddCommGroup G] [Fintype G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (t : ↥𝒩 → ℕ) (ht : IsIrreducible 𝒩 t) :
    ∑ g : ↥𝒩, t g ≤ Fintype.card G - 1 := by sorry

end Gomory69.Asymptotic
