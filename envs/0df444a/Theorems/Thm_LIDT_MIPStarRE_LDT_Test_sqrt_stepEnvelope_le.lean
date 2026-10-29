-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Test_sqrt_stepEnvelope_le
-- name    : LIDT.MIPStarRE.LDT.Test.sqrt_stepEnvelope_le
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:39:04.583537+00:00
-- url     : https://prove2.me/theorems/b351ae82-7561-4306-9f74-3581dc6d2187
-- title:
--   Sqrt Step Envelope Le
-- statement:
--   **Taking a square root doubles both parameters of the step envelope.**
--
--   Assume the scalar cascade hypotheses and let \(n>0\) and \(N>0\). For
--
--   $$
--   E_{n,N}=\varepsilon^{1/n}+\left(\frac dq\right)^{1/n}+\exp\!\left(-\frac{k}{Nm^2}\right),
--   $$
--
--   one has
--
--   $$
--   \sqrt{E_{n,N}}\le E_{2n,2N}.
--   $$
--
--   The proof applies the square-root subadditivity estimate to the three summands, uses the fractional-power identity for the first two, and halves the exponential rate by doubling \(N\).
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Test.sqrt_stepEnvelope_le`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean#L109-L127

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

theorem LIDT.MIPStarRE.LDT.Test.sqrt_stepEnvelope_le {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {n N : _root_.LIDT.MIPStarRE.LDT.Error} (hn : 0 < n) (hN : 0 < N) :
    Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps n N) ≤ _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2 * n) (2 * N) := by sorry
