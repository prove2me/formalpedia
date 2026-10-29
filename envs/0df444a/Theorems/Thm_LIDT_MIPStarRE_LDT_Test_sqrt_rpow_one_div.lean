-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Test_sqrt_rpow_one_div
-- name    : LIDT.MIPStarRE.LDT.Test.sqrt_rpow_one_div
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:33:51.459808+00:00
-- url     : https://prove2.me/theorems/46c32ddf-8b73-469c-8c8d-f3aaaba23094
-- title:
--   Sqrt Rpow One Div
-- statement:
--   **A square root halves the exponent of a nonnegative real power.**
--
--   For real numbers \(x\) and \(n\) with \(x\ge0\) and \(n>0\),
--
--   $$
--   \sqrt{x^{1/n}}=x^{1/(2n)},
--   $$
--
--   where the powers are real powers. This identity converts a square-root loss into the next fractional-power scale used by the step-envelope estimates.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Test.sqrt_rpow_one_div`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean#L91-L100

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Mathlib

open LIDT
/-!
# Error cascade — envelope and root bounding machinery

Internal helper lemmas for the error-cascade bookkeeping of Step 8.
These provide the step-envelope interpolation (`stepEnvelope`),
monotonicity under denominator enlargement, square-root scaling, and
explicit numeric bounds on various `rpow` and `sqrt` expressions.
All lemmas are technical and should not be part of downstream API.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section

open scoped BigOperators

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem LIDT.MIPStarRE.LDT.Test.sqrt_rpow_one_div {x n : _root_.LIDT.MIPStarRE.LDT.Error} (hx : 0 ≤ x) (_hn : 0 < n) :
    Real.sqrt (Real.rpow x (1 / n)) = Real.rpow x (1 / (2 * n)) := by sorry
