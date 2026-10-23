-- Prove2me | Theorems.Thm_LeanTT2_deq_undecidable
-- name    : LeanTT2.deq_undecidable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T03:08:36.487992+00:00
-- url     : https://prove2.me/theorems/38befa75-a250-4d91-ae76-e1c82c256630
-- title:
--   The definitional equality of the kernel is undecidable
-- statement:
--   For every extended fragment carrying the counterexample data of thesis section 3.1: there is no Boolean-valued function on contexts and pairs of terms that decides the ideal definitional equality in both directions. Given such a decider, its value at the context, the initial unfolding application, and the unit element would decide whether the step predicate is ever false: a true value yields a definitional equality with the unit element, which by the non-halting clause implies that the machine halts; and whenever the machine halts, the unfolding chain and the halting clause produce a definitional equality with the unit element, which the decider would report true. This decides the halting problem, which the counterexample data declares undecidable.
-- source:
--   M. Carneiro, The Type Theory of Lean, 2019, section 3.1 (p. 16).

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

/-!
# The definitional equality of the kernel is undecidable

Thesis section 3.1 (page 16): the ideal definitional equality of the
type system is undecidable. In the counterexample construction, the
value `f (num 0) acc0` is definitionally equal to the unit element
exactly when the step predicate `P` is false at some stage, that is,
exactly when the machine halts. If a Boolean decider of the definitional
equality existed in both directions, then its value at the context, the
term `f (num 0) acc0`, and the unit element would decide the halting of
the machine: a true value gives a definitional equality, and the
non-halting clause of the counterexample data would then produce a
contradiction; a false value together with a halted stage gives, by the
unfolding chain and the halting clause, a definitional equality that
the decider would have reported true. This contradicts the
undecidability of the halting problem, which the counterexample data
carries as the field `hundec`.
-/

namespace LeanTT2

/-- For every extended fragment carrying the counterexample data of
thesis section 3.1: there is no Boolean-valued function `dec` on
contexts and pairs of terms that decides the ideal definitional
equality in both directions. Such a decider would decide the halting of
the machine encoded in the step predicate, contradicting the
undecidability field of the counterexample data. -/
theorem deq_undecidable (F : Frag.{u}) (C : Counter F)
    (dec : F.Ctx → F.E → F.E → Bool)
    (hdec1 : ∀ (Γ : F.Ctx) (a b : F.E), F.deq Γ a b → dec Γ a b = true)
    (hdec2 : ∀ (Γ : F.Ctx) (a b : F.E), dec Γ a b = true → F.deq Γ a b) :
    False := by sorry

end LeanTT2
