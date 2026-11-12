-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_step4_relation_5076
-- name    : OddOrder.BG.AppC.FieldNormalizerData.step4_relation_5076
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:30:33.917518+00:00
-- url     : https://prove2.me/theorems/a49adb40-d7a1-4fc5-b295-a1bbec554282
-- title:
--   BG Lemma C.3, Step 4: kernel identity (5076) from relation (C.10)
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C, with $s=\sigma(1_{P_0})$, $t=ysy^{-1}$ ($y\in Q$ the distinguished element), and $\sigma(c)$ the image of $c\in\mathbb{Z}/p$ in the prime-field line $P_0$. Let $c_1,c_2,c_3\in\mathbb{Z}/p$ satisfy (C.10):
--   $$t^{2}\,\sigma(c_1)\,t^{-1}\,\sigma(c_2)\,t^{-1}\,\sigma(c_3)=1.$$
--   Then there exists $y_c\in G$ with $t=y_c^{-1}sy_c$ and
--   $$\sigma(c_1)\,\bigl(y_c^{-1}\sigma(c_1)^{-1}y_c\bigr)\,t^{-1}=t^{-1}\,\bigl(y_c^{-1}\sigma(c_3)^{-1}y_c\bigr)\,\sigma(c_3).$$
--
--   In Step 4 of Lemma C.3, the element $y$ lies in $[Q,W_2]$ and (C.10) places it in the kernel of a certain element of the group ring; the fixed-point-free action of $s$ (Remark (X)) removes a factor $(s^{-1}-1)$, leaving this identity (5076) with an explicit conjugator $y_c$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_FixedPointFree.lean#L210-L342

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

theorem step4_relation_5076 (data : FieldNormalizerData p q G) {c1 c2 c3 : ZMod p}
    (hC10 : data.t ^ 2 * data.sigma (primeLineElement p q c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q c3) = 1) :
    ∃ yc : G, data.t = yc⁻¹ * data.s * yc ∧
      data.sigma (primeLineElement p q c1) *
          (yc⁻¹ * (data.sigma (primeLineElement p q c1))⁻¹ * yc) * data.t⁻¹ =
        data.t⁻¹ * (yc⁻¹ * (data.sigma (primeLineElement p q c3))⁻¹ * yc) *
          data.sigma (primeLineElement p q c3) := by sorry

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
