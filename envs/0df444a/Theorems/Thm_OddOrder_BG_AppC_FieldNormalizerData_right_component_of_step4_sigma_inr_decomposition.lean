-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_right_component_of_step4_sigma_inr_decomposition
-- name    : OddOrder.BG.AppC.FieldNormalizerData.right_component_of_step4_sigma_inr_decomposition
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:24:00.640045+00:00
-- url     : https://prove2.me/theorems/cc5ba14c-2b35-4ba5-88ec-e14654464469
-- title:
--   BG Lemma C.3, Step 4: right component of a normal form equals $u_1v_1$
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C, with $s=\sigma(1_{P_0})$. Let $m,r\in\mathbb{Z}$, let $w,u_1,v_1$ be norm-one units of $\mathbb{F}_{p^q}$ (elements of the complement $U$), and let $c\in\mathbb{Z}/p$. If
--   $$ s^{m}\,\sigma(w)\,s^{r}=\sigma(u_1)\,\sigma(c)\,\sigma(v_1)$$
--   in $G$ (where $\sigma(c)$ is the image of $c$ in the prime-field line $P_0$), then
--   $$ w=u_1v_1.$$
--
--   This is the "mod $P$" bridge of Step 4 of Lemma C.3 in neutral form: reading the equation modulo the additive kernel $P$ gives the right-projection. It is reused for both the forward and backward $k=3$ equations of (C.5).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_ScalarCalculus.lean#L327-L377

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

theorem right_component_of_step4_sigma_inr_decomposition
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (w u₁ v₁ : NormSet.normOneUnits p q) (c : ZMod p)
    (hdec : data.s ^ m *
          data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q)) :
    w = u₁ * v₁ := by sorry

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
