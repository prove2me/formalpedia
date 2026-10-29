-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Test_sqrt_scaled_stepEnvelope_le
-- name    : LIDT.MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:46:41.764657+00:00
-- url     : https://prove2.me/theorems/d0946836-bdfa-4221-8c13-403d6843f7ca
-- title:
--   Sqrt Scaled Step Envelope Le
-- statement:
--   **A scaled step-envelope bound yields a scaled square-root bound.**
--
--   Assume the scalar cascade hypotheses, \(C\ge0\), \(n>0\), \(N>0\), and
--
--   $$
--   x\le Ck^2m^4E_{n,N}.
--   $$
--
--   Then
--
--   $$
--   \sqrt{x}\le\sqrt C\,k m^2E_{2n,2N}.
--   $$
--
--   The result combines the square-root monotonicity of the inequality with the step-envelope bound \(E_{n,N}\le E_{2n,2N}^2\). It is the scaling lemma used when converting quadratic dimension factors in the cascade.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean#L385-L425

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
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

theorem LIDT.MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps x C n N : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps)
    (hC : 0 ≤ C)
    (hx : x ≤ C * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps n N)
    (hn : 0 < n) (hN : 0 < N) :
    Real.sqrt x ≤
      Real.sqrt C * (k : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2 * n) (2 * N) := by sorry
