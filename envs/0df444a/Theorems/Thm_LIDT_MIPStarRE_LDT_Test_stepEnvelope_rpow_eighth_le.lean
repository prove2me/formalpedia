-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Test_stepEnvelope_rpow_eighth_le
-- name    : LIDT.MIPStarRE.LDT.Test.stepEnvelope_rpow_eighth_le
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:46:27.132119+00:00
-- url     : https://prove2.me/theorems/5a87e160-78c2-4822-9cc0-f5b491b7757c
-- title:
--   Step Envelope Rpow Eighth Le
-- statement:
--   **The eighth power of the first step envelope reaches the later cascade scale.**
--
--   Under the scalar cascade hypotheses,
--
--   $$
--   E_{2048,160000}^{1/8}\le E_{16384,1280000}.
--   $$
--
--   This is the result of three successive square-root bounds. The intermediate scales are \((4096,320000)\) and \((8192,640000)\), followed by \((16384,1280000)\).
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Test.stepEnvelope_rpow_eighth_le`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean#L349-L383

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

theorem LIDT.MIPStarRE.LDT.Test.stepEnvelope_rpow_eighth_le {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) :
    Real.rpow (_root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (16384 : _root_.LIDT.MIPStarRE.LDT.Error) (1280000 : _root_.LIDT.MIPStarRE.LDT.Error) := by sorry
