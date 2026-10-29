-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Test_zeta4_bound
-- name    : LIDT.MIPStarRE.LDT.Test.zeta4_bound
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T18:16:56.186419+00:00
-- url     : https://prove2.me/theorems/da0a7207-9fe2-43ed-a252-d42a40552bb8
-- title:
--   Zeta4 Bound
-- statement:
--   **The concrete fourth cascade error is absorbed by the public main error.**
--
--   Assume the scalar cascade hypotheses and let $\nu\ge0$ satisfy
--
--   $$
--   \nu\le10000k^2m^2\left(\varepsilon^{1/1024}+\left(\frac dq\right)^{1/1024}\right).
--   $$
--
--   If $\sigma,\zeta_1,\zeta_2,\zeta_3$ are the corresponding first four cascade values, then
--
--   $$
--   \zeta_4\le E_{\mathrm{main}}(m,q,d,k,\varepsilon).
--   $$
--
--   The proof applies the explicit enlarged-envelope bound and its monotonicity comparison with the public error envelope.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Test.zeta4_bound`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta4.lean#L157-L194

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

theorem LIDT.MIPStarRE.LDT.Test.zeta4_bound {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ ζ₃ : _root_.LIDT.MIPStarRE.LDT.Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))))
    (hσEq : σ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3 ζ₁ ζ₂) :
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta4 σ ζ₁ ζ₃ ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps := by sorry
