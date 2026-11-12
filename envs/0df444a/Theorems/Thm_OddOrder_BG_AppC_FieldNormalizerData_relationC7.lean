-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_relationC7
-- name    : OddOrder.BG.AppC.FieldNormalizerData.relationC7
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:27:02.315631+00:00
-- url     : https://prove2.me/theorems/5bd046c4-0b19-4bcf-b494-60f4ee57df30
-- title:
--   BG Appendix C (C.7): rearranged substitution relation in terms of $w_1,w_2,w_3$
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C, with $s=\sigma(1_{P_0})$, $t=ysy^{-1}$, and $\sigma(\cdot)$ denoting images in $G$ of elements of $H=P\rtimes U$. Let $a,b$ be norm-one units of $\mathbb{F}_{p^q}$ with $a^{-1}+b^{-1}=2$ in $\mathbb{F}_{p^q}$, and let `forms : Step4C5NormalForms data a b` be normal forms of the three (C.5) factors, with prime-line coordinates $c_1,c_2,c_3\in\mathbb{Z}/p$ and complement elements $w_1,w_2,w_3\in U$. Then
--   $$ t^{-1}\,\sigma(c_2)\,t^{-1}=\Bigl(\sigma(w_1)\,\sigma(c_3)\,\sigma(w_2)\,t^{2}\,\sigma(c_1)\,\sigma(w_3)\Bigr)^{-1}.$$
--
--   This is relation (C.7), obtained by rearranging the (C.5) substitution relation and absorbing the conjugated complement terms into $w_1,w_2,w_3$.
--
--   **Formalization Note** `Step4C5NormalForms` is a project structure bundling the normal-form data; $w_i$ are the fields `w1`, `w2`, `w3` of `forms`, and $\sigma(w)$ is `data.sigma (SemidirectProduct.inr w)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_NormalForms.lean#L680-L767

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_NormalForms

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

theorem relationC7
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) * data.t⁻¹ =
      (data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q forms.c3) *
          data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q) *
            data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
              data.sigma
                (SemidirectProduct.inr forms.w3 : NormSet.normOneFrobeniusGroup p q))⁻¹ := by sorry

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
