-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U
-- name    : OddOrder.BG.AppC.FieldNormalizerData.subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T04:52:24.852287+00:00
-- url     : https://prove2.me/theorems/e5d687b8-9008-4999-8b97-60d96028da21
-- title:
--   BG Lemma C.3, Step 3: a subgroup between $U$ and $PU$ is $U$ or $PU$
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C, with subgroups $P=\sigma(P)$ and $U=\sigma(U)$ of $G$. Let $X\le G$ be a subgroup with $U\le X\le P\sqcup U$ (the join $PU$) and $X\ne U$. Then
--   $$X=P\sqcup U.$$
--
--   Equivalently, any subgroup of $PU$ containing $U$ is either $U$ or all of $PU$. This transports the irreducibility of the concrete Frobenius group $P\rtimes U$ through $\sigma$, and is the irreducibility bridge used in Step 3 of Lemma C.3.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_Setup.lean#L405-L448

import Definitions.Def_OddOrder_BG_AppC_FrobeniusBasics
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup

namespace OddOrder.BG.AppC

open scoped Pointwise

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

theorem subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U
    (data : FieldNormalizerData p q G) {X : Subgroup G}
    (hUle : data.U ≤ X) (hXle : X ≤ data.P ⊔ data.U)
    (hne : X ≠ data.U) :
    X = data.P ⊔ data.U := by sorry

end FieldNormalizerData

end OddOrder.BG.AppC
