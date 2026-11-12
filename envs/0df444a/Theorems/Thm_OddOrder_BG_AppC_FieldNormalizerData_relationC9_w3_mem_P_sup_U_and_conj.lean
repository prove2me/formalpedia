-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_relationC9_w3_mem_P_sup_U_and_conj
-- name    : OddOrder.BG.AppC.FieldNormalizerData.relationC9_w3_mem_P_sup_U_and_conj
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:28:59.155823+00:00
-- url     : https://prove2.me/theorems/4f88b871-c20f-4afb-a36e-11015b07372e
-- title:
--   BG Appendix C (C.9): $S_1W_3^{p-1}S_1^{-1}$ and its $t^2$-conjugate lie in $PU$
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C (with $P,U\le G$, $t=ysy^{-1}$ and $\sigma(\cdot)$ as usual). Let $a,b$ be norm-one units of $\mathbb{F}_{p^q}$ such that $a^{-1}$ and $b^{-1}$ lie in the norm set $E=\{x\in\mathbb{F}_{p^q}: N(x)=N(2-x)=1\}$ and $a^{-1}+b^{-1}=2$, and let `forms : Step4C5NormalForms data a b` be normal forms of the three (C.5) factors, with prime-line coordinate $c_1$ and complement elements $w_1,w_2,w_3$. Put
--   $$S_1=\sigma(c_1),\qquad W_3^{\mathrm{pow}}=\sigma\bigl(w_3^{\,p-1}\bigr).$$
--   Then
--   $$S_1W_3^{\mathrm{pow}}S_1^{-1}\in P\sqcup U\quad\text{and}\quad t^{2}\bigl(S_1W_3^{\mathrm{pow}}S_1^{-1}\bigr)t^{-2}\in P\sqcup U.$$
--
--   This is relation (C.9) for the third word: comparing (C.7) for $(a,b)$ with (C.7) for $(a^p,b^p)$ gives these two memberships in $PU$.
--
--   **Formalization Note** $N$ is `NormSet.normN`, the norm set is `NormSet.normSetE p q`, and $P\sqcup U$ is the join of subgroups of $G$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_Step4Capstone.lean#L42-L157

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_NormalForms
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

theorem relationC9_w3_mem_P_sup_U_and_conj
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    let S1 := data.sigma (primeLineElement p q forms.c1)
    let W3pow := data.sigma
      (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
        NormSet.normOneFrobeniusGroup p q)
    S1 * W3pow * S1⁻¹ ∈ data.P ⊔ data.U ∧
      data.t ^ 2 * (S1 * W3pow * S1⁻¹) * (data.t ^ 2)⁻¹ ∈
        data.P ⊔ data.U := by sorry

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
