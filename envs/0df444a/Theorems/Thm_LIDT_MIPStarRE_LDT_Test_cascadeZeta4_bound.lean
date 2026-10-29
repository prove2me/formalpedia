-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeZeta4_bound
-- name    : LIDT.MIPStarRE.LDT.Test.cascadeZeta4_bound
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T18:09:34.347881+00:00
-- url     : https://prove2.me/theorems/2427c5db-b7ee-4bbc-b5a2-8730e1fc7a64
-- title:
--   Cascade Zeta4 Bound
-- statement:
--   **The fourth cascade error has an explicit enlarged-envelope bound.**
--
--   Assume the scalar cascade hypotheses and let $\nu\ge0$ obey
--
--   $$
--   \nu\le10000k^2m^2\left(\varepsilon^{1/1024}+\left(\frac dq\right)^{1/1024}\right).
--   $$
--
--   Let $\sigma,\zeta_1,\zeta_2,\zeta_3$ be the cascade values generated from $\nu$ and $\varepsilon$. Define
--
--   $$
--   E_{n,N}=\varepsilon^{1/n}+\left(\frac dq\right)^{1/n}+\exp\!\left(-\frac{k}{Nm^2}\right).
--   $$
--
--   Then
--
--   $$
--   \zeta_4\le40000\,k^2m^4E_{32768,2560000}.
--   $$
--
--   This is the intermediate large-scale estimate before comparing the enlarged envelope with the public main error.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Test.cascadeZeta4_bound`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta4.lean#L24-L155

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
# Error cascade — bound for `ζ₄`

This module contains the `ζ₄` cascade estimate used in Step 8 of the main
inductive step and its absorption into `mainFormalError`.

## References

* `references/ldt-paper/inductive_step.tex`, lines 220--228.
-/

@[expose] public section

open scoped BigOperators

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem LIDT.MIPStarRE.LDT.Test.cascadeZeta4_bound {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {ν : _root_.LIDT.MIPStarRE.LDT.Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)))) :
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta4 (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν)
        (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν))
        (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3
          (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν))
          (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2 (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν)))) ≤
      40000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (32768 : _root_.LIDT.MIPStarRE.LDT.Error) (2560000 : _root_.LIDT.MIPStarRE.LDT.Error) := by sorry
