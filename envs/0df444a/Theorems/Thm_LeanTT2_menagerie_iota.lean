-- Prove2me | Theorems.Thm_LeanTT2_menagerie_iota
-- name    : LeanTT2.menagerie_iota
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T03:04:55.345366+00:00
-- url     : https://prove2.me/theorems/fbb7a0b6-bcdb-483f-b5bb-393a997eddc3
-- title:
--   The eight iota rules of the menagerie hold in the ideal definitional equality
-- statement:
--   For every extended fragment, every context, and all terms a, b, e, f, x: the first projection of an explicit pair is definitionally equal to the first component; the second projection to the second component; the case analysis of the binary sum is definitionally equal to the left branch applied to the argument on the left injection, and to the right branch applied to the argument on the right injection; the universe unlift of a lifted term is definitionally the term; the W-recursor applied to an explicit supremum is definitionally equal to the step applied to the seed, the branching function, and the recursive continuation; the equality recursor computes on reflexivity; and the accessibility recursor computes on an explicit introduction, with the recursive continuation. These are the eight iota equations of page 28 of the thesis, lifted from the reduction relation to the ideal definitional equality.
-- source:
--   M. Carneiro, The Type Theory of Lean, 2019, section 5.1 (p. 28).

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

/-!
# The iota rules of the menagerie in the ideal definitional equality

The eight iota rules displayed on page 28 of Mario Carneiro's thesis
"The Type Theory of Lean" (2019), lifted from the reduction relation of
the fragment to the ideal definitional equality by the conversion
principle `red_deq`: the two projections of an explicit pair, the case
analysis of the binary sum on the two injections, the universe unlift
after a lift, the W-recursor on an explicit supremum (with the recursive
continuation `recW_cont` standing for the function
`b ↦ rec_W e (f b)`), the equality recursor on reflexivity, and the
accessibility recursor on an explicit introduction (with the recursive
continuation `recAcc_cont` standing for the function
`(y, h) ↦ rec_acc e y (f y h)`).
-/

namespace LeanTT2

/-- All eight iota rules of the menagerie (thesis page 28) hold in the
ideal definitional equality of every extended fragment: for every
context and all terms `a`, `b`, `e`, `f`, `x`, the displayed equations
hold up to `deq`. -/
theorem menagerie_iota (F : Frag.{u}) (Γ : F.Ctx) (a b e f x : F.E) :
    F.deq Γ (F.fst (F.pairT a b)) a ∧
    F.deq Γ (F.snd (F.pairT a b)) b ∧
    F.deq Γ (F.caseT a b (F.inl x)) (F.app a x) ∧
    F.deq Γ (F.caseT a b (F.inr x)) (F.app b x) ∧
    F.deq Γ (F.down (F.up x)) x ∧
    F.deq Γ (F.recW e (F.supT a f))
      (F.app (F.app (F.app e a) f) (F.recW_cont e f)) ∧
    F.deq Γ (F.recEq e a (F.reflT a)) e ∧
    F.deq Γ (F.recAcc e x (F.introAcc x f))
      (F.app (F.app (F.app e x) f) (F.recAcc_cont e f)) := by sorry

end LeanTT2
