-- Prove2me | Theorems.Thm_GroupFiniteness_ker_isFinitelyNormallyGenerated_of_surjective
-- name    : GroupFiniteness.ker_isFinitelyNormallyGenerated_of_surjective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T09:00:18.891639+00:00
-- url     : https://prove2.me/theorems/1303c564-7dda-4379-aa6d-85cf831f58bf
-- title:
--   A finitely presented group is presented on any finite generating set
-- statement:
--   Let $C$ be a finitely presented group and let $\chi : F_n \to C$ be a surjective
--   homomorphism from the free group on $n$ generators. Then $\ker \chi$ is the normal closure of a
--   finite subset of $F_n$, that is, $C$ is presented by the $n$ given generators subject to finitely
--   many relations.
--
--   Being finitely presented asserts the existence of *some* finite presentation; this says the
--   property does not depend on which finite generating set is chosen. Mathlib has the notion
--   `Subgroup.IsFinitelyNormallyGenerated` (a subgroup that is the normal closure of a finite set)
--   together with its behaviour under homomorphisms, and `Group.IsFinitelyPresented`, but not this
--   independence.
-- source:
--   Standard change-of-generators (Tietze) fact for finitely presented groups. Cited as Kurosh, Theory of Groups, vol. II, p. 73 by Milnor, Growth of finitely generated solvable groups, Journal of Differential Geometry 2 (1968) 448, https://doi.org/10.4310/jdg/1214428659, in the proof of Lemma 2; this statement is not asserted in that form by Milnor's note, which uses it.

import Mathlib

namespace GroupFiniteness

/-- A finitely presented group is presented on *any* finite generating set, with finitely many
relations: if `C` is finitely presented and `χ : FreeGroup (Fin n) →* C` is surjective, then
`ker χ` is the normal closure of a finite set. This is the change-of-generators step of Tietze's
theorem (B. H. Neumann). Mathlib has `Subgroup.IsFinitelyNormallyGenerated` with its behaviour
under maps, and `Group.IsFinitelyPresented` asserting the existence of *some* such presentation,
but not the independence of the chosen generating set. -/
theorem ker_isFinitelyNormallyGenerated_of_surjective {C : Type*} [Group C]
    [Group.IsFinitelyPresented C] {n : ℕ} (χ : FreeGroup (Fin n) →* C)
    (hχ : Function.Surjective χ) : χ.ker.IsFinitelyNormallyGenerated := by
  sorry

end GroupFiniteness
