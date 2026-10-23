-- Prove2me | Theorems.Thm_LeanTT2_inductive_to_w
-- name    : LeanTT2.inductive_to_w
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T03:09:15.66599+00:00
-- url     : https://prove2.me/theorems/c24727e4-c8f1-4324-b0d2-99bb50d502a8
-- title:
--   Inductive specifications are realized by W-types
-- statement:
--   Goal statement: for every extended fragment and every inductive specification, given a seed type A and a branching family B with their typing, a coverage embedding every constructor's seed type into A with branching definitionally equal to the constructor's recursive-arity family, the well-formedness of the W-type of the presentation, the subsingleton property of its truncation for small specifications, and a typed constructor family with a typed recursor satisfying the iota rule against the specification's step functions, there exists a W-type realization of the specification: a record with the seed A, the branching B, the W-type as the realized type, the constructors, and the recursor as the eliminator, satisfying the correctness predicate RealizesOK.
-- source:
--   M. Carneiro, The Type Theory of Lean, 2019, chapter 5 (pp. 27-32).

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

/-!
# Goal: inductive specifications are realized by W-types

The main goal of the mission, thesis chapter 5 (pages 27 to 32): every
inductive specification is realized by a W-type presentation. The
hypotheses supply the packing of the constructor shapes into a seed
type `A` with a branching family `B` covering every constructor (the
output of the constructor-packing milestone), the well-formedness of
the W-type (the output of the W-skeleton milestone), the subsingleton
property for small specifications (the output of the truncation
milestone), and a typed constructor family with a typed recursor
satisfying the iota rule against the specification's step functions.
The conclusion assembles the realization record: seed `A`, branching
`B`, the realized type `wT A B`, the constructors, and the eliminator,
and verifies the full correctness predicate `RealizesOK`.
-/

namespace LeanTT2

/-- Goal statement: for every extended fragment and every inductive
specification `Sp`, given a seed type `A` and a branching family `B`
with their typing, a coverage of every constructor's seed and branching
by the presentation, the well-formedness of the W-type `wT A B`, the
subsingleton property of its truncation when `Sp` is small, and a typed
constructor family `cs` with a typed recursor `r` satisfying the iota
rule against the specification's step functions, there exists a W-type
realization of `Sp` satisfying the correctness predicate `RealizesOK`. -/
theorem inductive_to_w (F : Frag.{u}) (Sp : IndSpec F)
    (A B : F.E)
    (hA : F.isType Sp.Γ A)
    (hB : F.ty Sp.Γ B (F.piT A F.Univ))
    (hcover : ∀ i : Fin Sp.n, ∃ c, F.ty Sp.Γ c (F.piT (Sp.SN i) A) ∧
      ∀ a, F.deq Sp.Γ (F.app B (F.app c a)) (F.app (Sp.SR i) a))
    (hskel : F.isType Sp.Γ (F.wT A B))
    (hsub : Sp.small = true → F.isProp Sp.Γ (F.truncT (F.wT A B)))
    (hreal : ∃ (cs : Fin Sp.n → F.E) (r : F.E),
      (∀ i : Fin Sp.n, F.ty Sp.Γ (cs i) (Sp.CTy i)) ∧
      F.ty Sp.Γ r (F.piT (F.wT A B) Sp.RecTy) ∧
      (∀ (i : Fin Sp.n) (x : F.E),
        F.red Sp.Γ (F.app r (F.app (cs i) x)) (F.app (Sp.step i) x))) :
    ∃ R : Realizes F Sp, RealizesOK F Sp R := by sorry

end LeanTT2
