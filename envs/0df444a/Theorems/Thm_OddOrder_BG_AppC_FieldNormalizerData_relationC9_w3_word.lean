-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_relationC9_w3_word
-- name    : OddOrder.BG.AppC.FieldNormalizerData.relationC9_w3_word
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:29:11.141789+00:00
-- url     : https://prove2.me/theorems/7d987c3c-d675-4c9e-8a1f-985e7ce97365
-- title:
--   BG Appendix C (C.9): the exact word equation for $W_3^{p-1}$
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C ($t=ysy^{-1}$, $\sigma(\cdot)$ the images of elements of $P\rtimes U$). Let $a,b$ be norm-one units of $\mathbb{F}_{p^q}$ with $a^{-1},b^{-1}$ in the norm set $E=\{x:N(x)=N(2-x)=1\}$ and $a^{-1}+b^{-1}=2$, and let `forms : Step4C5NormalForms data a b` be normal forms of the (C.5) factors with prime-line coordinates $c_1,c_3$ and complement elements $w_1,w_2,w_3$. Set
--   $S_1=\sigma(c_1)$, $S_3=\sigma(c_3)$, $W_i=\sigma(w_i)$ for $i=1,2$, $W_i^{p}=\sigma(w_i^{\,p})$ for $i=1,2$, and $W_3^{\mathrm{pow}}=\sigma(w_3^{\,p-1})$. Then
--   $$ (t^2)^{-1}\Bigl((W_2^{p})^{-1}S_3^{-1}(W_1^{p})^{-1}\,W_1\,S_3\,W_2\Bigr)t^{2}=S_1\,W_3^{\mathrm{pow}}\,S_1^{-1}.$$
--
--   This is the equality displayed just before (C.9): after comparing (C.7) with the Frobenius-powered (C.7), the remaining $w_1/w_2$ word is a $t^2$-conjugate of $S_1W_3^{p-1}S_1^{-1}$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_Step4Capstone.lean#L160-L264

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_NormalForms
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

theorem relationC9_w3_word
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    let S1 := data.sigma (primeLineElement p q forms.c1)
    let S3 := data.sigma (primeLineElement p q forms.c3)
    let W1 := data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q)
    let W2 := data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q)
    let W1p := data.sigma
      (SemidirectProduct.inr (forms.w1 ^ p) : NormSet.normOneFrobeniusGroup p q)
    let W2p := data.sigma
      (SemidirectProduct.inr (forms.w2 ^ p) : NormSet.normOneFrobeniusGroup p q)
    let W3pow := data.sigma
      (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
        NormSet.normOneFrobeniusGroup p q)
    (data.t ^ 2)⁻¹ * (W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2) * data.t ^ 2 =
      S1 * W3pow * S1⁻¹ := by sorry

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
