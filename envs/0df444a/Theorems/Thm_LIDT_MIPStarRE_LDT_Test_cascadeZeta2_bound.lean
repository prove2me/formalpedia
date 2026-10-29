-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeZeta2_bound
-- name    : LIDT.MIPStarRE.LDT.Test.cascadeZeta2_bound
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:56:33.662539+00:00
-- url     : https://prove2.me/theorems/2cb169c9-599c-4e36-bd86-63e7cde30b0f
-- title:
--   Cascade Zeta2 Bound
-- statement:
--   **The second cascade value is bounded by the quarter-root step envelope.**
--
--   Assume the cascade hypotheses, nonnegative `nu`, and the coarse bound on `nu`. With the first cascade value evaluated from `eps` and the cascade value, the second cascade quantity satisfies
--
--   $$
--   \operatorname{cascadeZeta2}(\operatorname{cascadeZeta1}(\mathrm{params},\varepsilon,\operatorname{cascadeSigma}(\mathrm{params},k,\nu)))
--   \le2568\,k m\,\operatorname{stepEnvelope}(\mathrm{params},k,\varepsilon,16384,1280000).
--   $$
--
--   The estimate combines the first-stage bound with the fractional-power inequalities for the second stage. It is the internal input to the public second-stage and later third-stage bounds.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Test.cascadeZeta2_bound`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta2Zeta3.lean#L25-L80

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Test
end LIDT.MIPStarRE.LDT.Test

open LIDT
/-!
# Error cascade — bounds for `ζ₂` and `ζ₃`

This module contains the middle cascade estimates used in Step 8 of the main
inductive step: the absorbing bounds for `ζ₂` and `ζ₃` obtained from the
`σ` and `ζ₁` estimates.

## References

* `references/ldt-paper/inductive_step.tex`, lines 205--217 and 230.
-/

@[expose] public section

open scoped BigOperators

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem LIDT.MIPStarRE.LDT.Test.cascadeZeta2_bound {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {ν : _root_.LIDT.MIPStarRE.LDT.Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)))) :
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2 (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν)) ≤
      2568 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (16384 : _root_.LIDT.MIPStarRE.LDT.Error) (1280000 : _root_.LIDT.MIPStarRE.LDT.Error) := by sorry
