-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_relationC9_w1_w2_pow_sub_one_eq_one_of_w3_eq_one
-- name    : OddOrder.BG.AppC.FieldNormalizerData.relationC9_w1_w2_pow_sub_one_eq_one_of_w3_eq_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:28:58.01078+00:00
-- url     : https://prove2.me/theorems/e7d45031-0c2f-493d-ba30-62a1ff9d4a6e
-- title:
--   BG Appendix C (C.9): if $w_3=1$ then $w_1^{p-1}=w_2^{p-1}=1$
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C. Let $a,b$ be norm-one units of $\mathbb{F}_{p^q}$ with $a^{-1},b^{-1}$ in the norm set $E=\{x:N(x)=N(2-x)=1\}$ and $a^{-1}+b^{-1}=2$, and let `forms : Step4C5NormalForms data a b` be normal forms of the three (C.5) factors, with prime-line coordinates $c_i\in\mathbb{Z}/p$ and complement elements $w_1,w_2,w_3$. Assume $c_3\ne0$ and $w_3=1$. Then
--   $$w_1^{\,p-1}=1\quad\text{and}\quad w_2^{\,p-1}=1.$$
--
--   After the third word has been killed, the exact (C.9) word equation and Step 2 force the other two words to satisfy condition (A). The nontriviality $c_3\ne0$ is the (C.6) input, kept as an explicit hypothesis.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_Step4Capstone.lean#L266-L410

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_NormalForms
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

theorem relationC9_w1_w2_pow_sub_one_eq_one_of_w3_eq_one
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc3 : forms.c3 ≠ 0) (hw3 : forms.w3 = 1) :
    forms.w1 ^ (p - 1) = 1 ∧ forms.w2 ^ (p - 1) = 1 := by sorry

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
