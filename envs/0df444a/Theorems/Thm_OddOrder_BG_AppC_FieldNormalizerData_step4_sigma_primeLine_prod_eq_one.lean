-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_step4_sigma_primeLine_prod_eq_one
-- name    : OddOrder.BG.AppC.FieldNormalizerData.step4_sigma_primeLine_prod_eq_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:29:48.795094+00:00
-- url     : https://prove2.me/theorems/9012f5ff-fe12-4a76-8b58-28829349853c
-- title:
--   BG Lemma C.3, Step 4: relation (C.10) collapses to $s_1s_2s_3=1$
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C, with $s=\sigma(1_{P_0})$, $t=ysy^{-1}$ ($y\in Q$ the distinguished element), and $\sigma(c)$ the image of $c\in\mathbb{Z}/p$ in the prime-field line $P_0$. Let $c_1,c_2,c_3\in\mathbb{Z}/p$ and suppose relation (C.10) holds:
--   $$t^{2}\,\sigma(c_1)\,t^{-1}\,\sigma(c_2)\,t^{-1}\,\sigma(c_3)=1.$$
--   Then
--   $$\sigma(c_1)\,\sigma(c_2)\,\sigma(c_3)=1.$$
--
--   This is (C.10) reduced modulo $Q$ in Step 4 of Lemma C.3: since $P_0\cap Q=1$ and $t\equiv s\pmod Q$, the relation collapses to the product relation $s_1s_2s_3=1$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_FixedPointFree.lean#L85-L179

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

theorem step4_sigma_primeLine_prod_eq_one (data : FieldNormalizerData p q G) {c1 c2 c3 : ZMod p}
    (hC10 : data.t ^ 2 * data.sigma (primeLineElement p q c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q c3) = 1) :
    data.sigma (primeLineElement p q c1) *
        data.sigma (primeLineElement p q c2) *
          data.sigma (primeLineElement p q c3) = 1 := by sorry

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
