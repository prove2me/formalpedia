-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_Step4C5NormalForms_c1_ne_zero
-- name    : OddOrder.BG.AppC.FieldNormalizerData.Step4C5NormalForms.c1_ne_zero
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:26:46.799945+00:00
-- url     : https://prove2.me/theorems/6e6fce7f-395b-4fb8-864e-44d94ea519fa
-- title:
--   BG Appendix C (C.6): the first prime-line coordinate is nonzero
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C, let $a,b$ be norm-one units of $\mathbb{F}_{p^q}$, and let `forms : Step4C5NormalForms data a b` be a choice of normal forms for the three factors of relation (C.5) (each factor written as $\sigma(u_i)\,\sigma(c_i)\,\sigma(v_i)$ with $c_i\in\mathbb{Z}/p$ the prime-line coordinate and $u_i,v_i$ norm-one units). Then the first prime-line coordinate is nonzero:
--   $$c_1\ne0\quad\text{in }\mathbb{Z}/p.$$
--
--   This is the part of (C.6) for the first factor: if $c_1=0$, the first normal form lies in $U$, and reading the same element as $s\cdot U\cdot s^{-2}$ and applying Step 2 with prime-line coordinates $(1,-2)$ gives $1=0$ or $-1=0$ in $\mathbb{Z}/p$.
--
--   **Formalization Note** `Step4C5NormalForms data a b` is a structure bundling the coordinates $c_i$, units $u_i,v_i$, the three normal-form equations, and the identifications of the right components of the three factors with $u_iv_i$; the theorem holds for any such structure.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_NormalForms.lean#L573-L624

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_NormalForms

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

namespace Step4C5NormalForms

theorem c1_ne_zero {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    forms.c1 ≠ 0 := by sorry

end Step4C5NormalForms

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
