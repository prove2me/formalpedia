-- Prove2me | Theorems.Thm_LeanTT2_algo_not_transitive
-- name    : LeanTT2.algo_not_transitive
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T03:07:17.997759+00:00
-- url     : https://prove2.me/theorems/4adca8a5-02e3-4802-8a63-de0011db99a4
-- title:
--   The algorithmic equality of the kernel is not transitive
-- statement:
--   For every extended fragment carrying the counterexample data of thesis section 3.1: there are three terms a, b, c such that the algorithmic equality of the kernel relates a to b and b to c, but not a to c. In the thesis, the three terms are the initial application of the unfolding function, its creative middle step, and the application at the next numeral; the algorithm never attempts the composite step because the initial application is a normal form. The algorithmic equality is not transitive.
-- source:
--   M. Carneiro, The Type Theory of Lean, 2019, section 3.1.1 (p. 17).

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

/-!
# The algorithmic equality of the kernel is not transitive

Thesis section 3.1.1 (page 17): the algorithmic equality implemented by
the Lean kernel is not transitive. In the construction of section 3.1,
the term `f 0 a` is algorithmically equal to `f 0 (intro_acc 0 (inv_0 a))`,
which is algorithmically equal to `f 1 (inv_0 a 1 (p 0))`, but the outer
pair is not: the middle step is "creative", and since `f 0 a` is a normal
form the algorithm never attempts it. The counterexample data of the
fragment carries the three witnesses abstractly.
-/

namespace LeanTT2

/-- For every extended fragment carrying the counterexample data of
thesis section 3.1: there are three terms `a`, `b`, `c` such that the
algorithmic equality relates `a` to `b` and `b` to `c`, but not `a` to
`c`. The algorithmic equality of the kernel is not transitive. -/
theorem algo_not_transitive (F : Frag.{u}) (C : Counter F) :
    ∃ a b c, F.alg C.Γ a b ∧ F.alg C.Γ b c ∧ ¬ F.alg C.Γ a c := by sorry

end LeanTT2
