-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_Step4C5NormalForms_c3_ne_zero
-- name    : OddOrder.BG.AppC.FieldNormalizerData.Step4C5NormalForms.c3_ne_zero
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:26:32.685246+00:00
-- url     : https://prove2.me/theorems/105be447-83b1-476d-9b86-fb01e0099637
-- title:
--   BG Appendix C (C.6): the third prime-line coordinate is nonzero
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C, let $a,b$ be norm-one units of $\mathbb{F}_{p^q}$, and let `forms : Step4C5NormalForms data a b` be a choice of normal forms for the three factors of relation (C.5) (each written $\sigma(u_i)\,\sigma(c_i)\,\sigma(v_i)$ with $c_i\in\mathbb{Z}/p$). Then
--   $$c_3\ne0\quad\text{in }\mathbb{Z}/p.$$
--
--   This is the part of (C.6) for the third factor: if $c_3=0$, the third normal form lies in $U$; reading the same element as $s^{2}\cdot U\cdot s^{-3}$ and applying Step 2 with prime-line coordinates $(2,-3)$ gives $2=0$ or $-1=0$ in $\mathbb{Z}/p$, both impossible.
--
--   **Formalization Note** `Step4C5NormalForms data a b` is a structure bundling the coordinates $c_i$, units $u_i,v_i$, the normal-form equations, and the identification of the right components.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_NormalForms.lean#L626-L676

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

theorem c3_ne_zero {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    forms.c3 ≠ 0 := by sorry

end Step4C5NormalForms

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
