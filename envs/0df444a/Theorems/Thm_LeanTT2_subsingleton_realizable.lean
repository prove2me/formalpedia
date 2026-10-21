-- Prove2me | Theorems.Thm_LeanTT2_subsingleton_realizable
-- name    : LeanTT2.subsingleton_realizable
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T03:06:56.936872+00:00
-- url     : https://prove2.me/theorems/ed93180d-c671-4e9f-bf99-049fecaa1891
-- title:
--   The propositional truncation of a W-type is a proposition
-- statement:
--   For every extended fragment, context, and branching presentation A, B with A a type and B typed at the function type from A into the universe: the propositional truncation of the W-type of the presentation is a type, and it is a proposition. The truncation is the nonempty operation of thesis section 5.1, the tool that constructs small eliminators in the reduction of chapter 5.
-- source:
--   M. Carneiro, The Type Theory of Lean, 2019, sections 5.1 and 5.3 (pp. 27, 31).

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

/-!
# Subsingleton truncations of W-types

The propositional truncation of a W-type is a type and a proposition.
The truncation former is the nonempty operation of thesis section 5.1
(page 27), which produces a proposition from any type; it is the tool
used to construct small eliminators, and the subsingleton clause of the
realization correctness predicate is its counterpart (thesis section
5.3, page 31).
-/

namespace LeanTT2

/-- For every extended fragment, context, and branching presentation
`A`, `B` with `A` a type and `B` typed at `A → Univ`: the propositional
truncation of the W-type `wT A B` is a type, and it is a proposition. -/
theorem subsingleton_realizable (F : Frag.{u}) (Γ : F.Ctx) (A B : F.E)
    (hA : F.isType Γ A) (hB : F.ty Γ B (F.piT A F.Univ)) :
    F.isType Γ (F.truncT (F.wT A B)) ∧
    F.isProp Γ (F.truncT (F.wT A B)) := by sorry

end LeanTT2
