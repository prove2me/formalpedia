-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Test_rpow_Z1_factor_le
-- name    : LIDT.MIPStarRE.LDT.Test.rpow_Z1_factor_le
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:39:15.085256+00:00
-- url     : https://prove2.me/theorems/9a3e0afe-d966-4dec-88a6-37ffdcc9900d
-- title:
--   Rpow Z1 Factor Le
-- statement:
--   **A fractional power of the first cascade bound factors into separate controls.**
--
--   Let $Z_1,k_2,m_4,E_{2048},r,C_r,E_r$ be nonnegative real quantities. Assume
--
--   $$
--   Z_1\le20204\,k_2m_4E_{2048},
--   $$
--
--   and
--
--   $$
--   (20204)^r\le C_r,\qquad k_2^r\le k,\qquad m_4^r\le m,\qquad E_{2048}^r\le E_r.
--   $$
--
--   Then
--
--   $$
--   Z_1^r\le C_r\,k\,m\,E_r.
--   $$
--
--   The lemma distributes the nonnegative real power across the product and applies the four supplied factor bounds. It is the bookkeeping step used in the quarter-power and repaired fourth-stage estimates.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Test.rpow_Z1_factor_le`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean#L427-L491

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

theorem LIDT.MIPStarRE.LDT.Test.rpow_Z1_factor_le {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ}
    {Z1 k2 m4 E2048 r Crpow Erpow : _root_.LIDT.MIPStarRE.LDT.Error}
    (hZ1NN : 0 ≤ Z1)
    (hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048)
    (hrNN : 0 ≤ r)
    (hk2NN : 0 ≤ k2)
    (hm4NN : 0 ≤ m4)
    (hE2048NN : 0 ≤ E2048)
    (hA : Real.rpow (20204 : _root_.LIDT.MIPStarRE.LDT.Error) r ≤ Crpow)
    (hB : Real.rpow k2 r ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error))
    (hC : Real.rpow m4 r ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error))
    (hD : Real.rpow E2048 r ≤ Erpow) :
    Real.rpow Z1 r ≤ Crpow * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Erpow := by sorry
