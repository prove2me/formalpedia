-- Prove2me | Theorems.Thm_LeanTT2_ctor_packing
-- name    : LeanTT2.ctor_packing
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-21T03:05:30.430987+00:00
-- url     : https://prove2.me/theorems/6cd68b60-7d7e-444f-a5ba-ba6f83ead8bf
-- title:
--   Constructor shapes pack into a single W-type seed
-- statement:
--   For every extended fragment and every inductive specification: there are a seed type A and a branching family B such that A is a type and B is typed at the function type from A into the universe, and for every constructor of the specification there is a coercion from the constructor's seed type into A such that, for every seed value, the branching of B at the coercion's value is definitionally equal to the constructor's recursive-arity family at that seed. This is the packing step of thesis section 5.1: the argument telescopes are packed into sigma types and the constructors into sums, so that a single W-type carries the whole specification.
-- source:
--   M. Carneiro, The Type Theory of Lean, 2019, section 5.1 (p. 27).

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

/-!
# Constructor packing: the constructor shapes of an inductive specification

Thesis section 5.1 (page 27) reduces an inductive type to a W-type by
packing: "most of the telescopes x :: α in an inductive type can be
replaced by Σ(x :: α) ... Similarly, we want the types 0 and α + β to
pack up all the constructors into one." The milestone states the
existence half of this packing for an arbitrary inductive specification
of the fragment: there are a seed type `A` and a branching family
`B : A → Univ` such that every constructor's seed type embeds into `A`,
and the branching of `B` at the image of a constructor seed is
definitionally the constructor's recursive-arity family.
-/

namespace LeanTT2

/-- For every extended fragment and every inductive specification: there
are a seed type `A` and a branching family `B`, with `A` a type and `B`
typed at `A → Univ`, such that for every constructor there is a coercion
`c` from the constructor's seed type into `A` whose branching under `B`
is definitionally the constructor's recursive-arity family. -/
theorem ctor_packing (F : Frag.{u}) (Sp : IndSpec F) :
    ∃ A B, F.isType Sp.Γ A ∧ F.ty Sp.Γ B (F.piT A F.Univ) ∧
      ∀ i : Fin Sp.n, ∃ c, F.ty Sp.Γ c (F.piT (Sp.SN i) A) ∧
        ∀ a, F.deq Sp.Γ (F.app B (F.app c a)) (F.app (Sp.SR i) a) := by sorry

end LeanTT2
