-- Prove2me | Theorems.Thm_LefebvreVariations_frankl_union_inter_closed
-- name    : LefebvreVariations.frankl_union_inter_closed
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:51:27.819909+00:00
-- url     : https://prove2.me/theorems/9d163286-9524-49e7-b2cd-11875e3d20e9
-- title:
--   Lefebvre's variations, No. 30 — on a theme by Frankl: Frankl's conjecture for families closed under unions and intersections
-- statement:
--   This is Frankl's union-closed sets conjecture for families that are closed under both unions and intersections.
--
--   Let $\mathcal F$ be a finite family of finite sets, different from $\emptyset$ and $\{\emptyset\}$, such that $A\cup B\in\mathcal F$ and $A\cap B\in\mathcal F$ whenever $A,B\in\mathcal F$. Then some element $x$ lies in at least half of the members of $\mathcal F$:
--
--   $$
--   \#\{A\in\mathcal F:\ x\in A\}\ \ge\ \tfrac12\,|\mathcal F| .
--   $$
--
--   Take a nonempty member $B$ of least size; by intersection-closure every member either contains $B$ or is disjoint from it, and for $x\in B$ the map $A\mapsto A\cup B$ injects the members avoiding $x$ into those containing $x$.
--
--   Frankl's conjecture asserts this for every union-closed family; in the lattice formulation, families closed under both operations are the distributive lattices of sets, one of the first classes for which it was established.
--
--   **Formalization Note** Union-closure, nondegeneracy and density are the mission's definitions; density divides by the number of members.
--
--   **Why this is a variation.** This varies the union-closed sets conjecture (Frankl), which says that some element lies in at least half of the members of a nondegenerate union-closed finite family. It is a special case: families closed under both union and intersection, that is, distributive lattices, where the conjecture holds. It removes a whole class of structured families from the search for a counterexample to the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Lattice formulation and the distributive case: H. Bruhn and O. Schaudt, The journey of the union-closed sets conjecture, Graphs Combin. 31 (2015), 2043–2074 (survey, lattice-theoretic section); B. Poonen, Union-closed families, J. Combin. Theory Ser. A 59 (1992), 253–268. Conjecture: P. Frankl, 1979. Parent problem: TenChallenges.challenge_09 (union-closed sets conjecture).

import Mathlib
import Definitions.Def_TenChallenges_Challenge_09

namespace LefebvreVariations

/-- The union-closed sets conjecture (Challenge 09) for rings of sets: if a nondegenerate
finite family is closed under union AND intersection (the sublattices of the Boolean
lattice, i.e. the distributive lattices), some element lies in at least half of its
members. A minimal nonempty member `B` meets every member in `∅` or in `B`, so
`A ↦ A ∪ B` injects the members avoiding a point `x ∈ B` into the members containing it.
Source: the distributive-lattice case of Frankl's conjecture, recorded in Bruhn and
Schaudt, "The journey of the union-closed sets conjecture", Graphs Combin. 31 (2015),
2043-2074 (section on lattices; going back to Poonen, "Union-closed families",
J. Combin. Theory Ser. A 59 (1992), 253-268, and Reinhold, "Frankl's conjecture is
true for lower semimodular lattices", Graphs Combin. 16 (2000), 115-116). -/
theorem frankl_union_inter_closed {U : Type*} [DecidableEq U] (F : Finset (Finset U))
    (hU : IsUnionClosed F)
    (hI : ∀ ⦃A B : Finset U⦄, A ∈ F → B ∈ F → A ∩ B ∈ F)
    (hne : Nondegenerate F) :
    ∃ x, density F x ≥ (1 / 2 : ℚ) := by
  sorry

end LefebvreVariations
