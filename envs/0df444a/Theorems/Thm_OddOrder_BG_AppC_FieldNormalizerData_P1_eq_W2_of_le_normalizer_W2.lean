-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_P1_eq_W2_of_le_normalizer_W2
-- name    : OddOrder.BG.AppC.FieldNormalizerData.P1_eq_W2_of_le_normalizer_W2
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:22:27.232804+00:00
-- url     : https://prove2.me/theorems/333c910b-a902-408c-aa0e-7d91491aee05
-- title:
--   BG Appendix C, Step 3: if $P_1$ normalizes $W_2$ then $P_1=W_2$
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C ($p$ prime, $G$ a group), with its subgroups $W_2=\sigma(P_0)$ (the image of the prime-field line) and $P_1$ (the conjugate of $W_2$ by the distinguished element $y\in Q$ of Hypothesis (B)). If $P_1\le N_G(W_2)$, then
--   $$P_1=W_2.$$
--
--   This is the final product/Sylow argument of Step 3 of Lemma C.3: $W_2P_1$ would be a $p$-subgroup of $W_2Q$, and since $Q$ is a $p'$-group and $|W_2|=p$, the $p$-part of $W_2Q$ has order exactly $p$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean#L928-L984

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine

namespace OddOrder.BG.AppC

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

theorem P1_eq_W2_of_le_normalizer_W2
    (data : FieldNormalizerData p q G)
    (hP1W2 : data.P1 ≤ Subgroup.normalizer (data.W2 : Set G)) :
    data.P1 = data.W2 := by sorry

end FieldNormalizerData

end OddOrder.BG.AppC
