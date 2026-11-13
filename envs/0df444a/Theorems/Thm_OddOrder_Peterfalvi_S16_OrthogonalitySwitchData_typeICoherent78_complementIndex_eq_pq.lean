-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_typeICoherent78_complementIndex_eq_pq
-- name    : OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.typeICoherent78_complementIndex_eq_pq
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:35:54.544352+00:00
-- url     : https://prove2.me/theorems/bd3ebb05-f373-4334-a404-691e24edf7cb
-- title:
--   Peterfalvi (14.3): the complement index of any coherence bundle on $L$ equals $pq$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group and `hyp` a Peterfalvi §14 configuration with primes $p,q$. Let `Ldata : LHypothesis hyp` be an $L$-side hypothesis (a type-I maximal subgroup `Ldata.L` over $N_G(U)$) and `dataL : TypeICoherent78Data Ldata.L` any (7.8) coherence bundle on $L$. Then the complement index satisfies
--   $$(\texttt{dataL.h78 hG}).\texttt{complementIndex} \;=\; p\,q .$$
--
--   Both the complement index $[L:\text{kernel}]$ of the coherence bundle and the order of the (14.3) Frobenius complement of $L$ are indices of the same canonical kernel $H_L$ (the maximal normal nilpotent Hall subgroup), and the latter equals $pq$ by (14.3).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLMBasic.lean#L544-L586

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem typeICoherent78_complementIndex_eq_pq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp) (dataL : TypeICoherent78Data Ldata.L) :
    (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q := by sorry

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
