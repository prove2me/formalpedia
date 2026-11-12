-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_step4_sigma_primeLine_eq_s_inv
-- name    : OddOrder.BG.AppC.FieldNormalizerData.step4_sigma_primeLine_eq_s_inv
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:29:51.491921+00:00
-- url     : https://prove2.me/theorems/c1b1043f-8c58-4721-bf1e-91007390e41b
-- title:
--   BG Lemma C.3, Step 4: the relation (5076) forces $\sigma(c_1)=s^{-1}$
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C, write $s=\sigma(1_{P_0})$ and $t=ysy^{-1}$ with $y\in Q$ as in Hypothesis (B), and for $c\in\mathbb{Z}/p$ let $\sigma(c)$ denote the image under $\sigma$ of the element $c$ of the prime-field line $P_0$. Let $c_1,c_3\in\mathbb{Z}/p$ with $c_1\ne0$ (and $c_3\ne 0$, an unused hypothesis), and let $y_c\in G$ satisfy $t=y_c^{-1}sy_c$. Suppose
--   $$\sigma(c_1)\,\bigl(y_c^{-1}\sigma(c_1)^{-1}y_c\bigr)\,t^{-1}=t^{-1}\,\bigl(y_c^{-1}\sigma(c_3)^{-1}y_c\bigr)\,\sigma(c_3).$$
--   Then
--   $$\sigma(c_1)=s^{-1}.$$
--
--   This is the conclusion of Step 4 of Lemma C.3: the relation (5076), $s_1t_1^{-1}t^{-1}=t^{-1}t_3^{-1}s_3$ with $t_i=y_c^{-1}s_iy_c$, forces $t_1=t^{-1}$ and hence $s_1=s^{-1}$, since otherwise Step 3 would give a contradiction with (C.6).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_FixedPointFree.lean#L421-L523

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

theorem step4_sigma_primeLine_eq_s_inv (data : FieldNormalizerData p q G)
    {c1 c3 : ZMod p}
    (hc1 : c1 ≠ 0) (_hc3 : c3 ≠ 0) (yc : G) (hty : data.t = yc⁻¹ * data.s * yc)
    (hrel : data.sigma (primeLineElement p q c1) *
        (yc⁻¹ * (data.sigma (primeLineElement p q c1))⁻¹ * yc) * data.t⁻¹ =
      data.t⁻¹ * (yc⁻¹ * (data.sigma (primeLineElement p q c3))⁻¹ * yc) *
        data.sigma (primeLineElement p q c3)) :
    data.sigma (primeLineElement p q c1) = data.s⁻¹ := by sorry

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
