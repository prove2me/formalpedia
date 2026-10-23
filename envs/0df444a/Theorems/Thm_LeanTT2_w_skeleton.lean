-- Prove2me | Theorems.Thm_LeanTT2_w_skeleton
-- name    : LeanTT2.w_skeleton
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T03:06:16.810668+00:00
-- url     : https://prove2.me/theorems/e2d519b7-95e6-4f51-a8a5-394062865135
-- title:
--   The W-type of a branching presentation and the computation of its recursor
-- statement:
--   For every extended fragment, context, and branching presentation A, B with A a type and B typed at the function type from A into the universe: the W-type of the presentation is a type, and for all terms e, a, f the W-recursor applied to the supremum of the seed a and the branching f is definitionally equal to the step e applied to the seed, the branching, and the recursive continuation of the recursor at f.
-- source:
--   M. Carneiro, The Type Theory of Lean, 2019, section 5.1 (pp. 27-28).

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

/-!
# The W-type skeleton and the computation of its recursor

The W-type of a branching presentation is a type, and the W-recursor
computes on an explicit supremum as in the iota rule of thesis page 28:
`rec_W e (sup a f) ≡ e a f (λ b. rec_W e (f b))`, with the recursive
continuation packaged by the field `recW_cont` of the fragment.
-/

namespace LeanTT2

/-- For every extended fragment, context, and branching presentation
`A`, `B` with `A` a type and `B` typed at `A → Univ`: the W-type
`wT A B` is a type, and for all terms `e`, `a`, `f` the W-recursor
applied to the supremum `supT a f` is definitionally equal to the step
`e` applied to the seed, the branching function, and the recursive
continuation `recW_cont e f`. -/
theorem w_skeleton (F : Frag.{u}) (Γ : F.Ctx) (A B : F.E)
    (hA : F.isType Γ A) (hB : F.ty Γ B (F.piT A F.Univ)) :
    F.isType Γ (F.wT A B) ∧
    ∀ e a f, F.deq Γ (F.recW e (F.supT a f))
      (F.app (F.app (F.app e a) f) (F.recW_cont e f)) := by sorry

end LeanTT2
