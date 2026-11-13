-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_coh_extension_sub_zeta0_eq_typeIBetaL_sub
-- name    : OddOrder.Peterfalvi.S15.coh_extension_sub_zeta0_eq_typeIBetaL_sub
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:23:23.548541+00:00
-- url     : https://prove2.me/theorems/592e5fc9-0802-4305-8821-b170280a49e6
-- title:
--   The $\varphi$-invariance identity $\varphi^{\tau_1}-\zeta_0^{\tau_1}=\beta_L^\tau(\zeta_0)-\beta_L^\tau(\varphi)$
-- statement:
--   Let $G$ be a finite group with `IsMinimalSimpleOdd G`, let $L\le G$ carry `dataL : TypeICoherent78Data L` with coherent extension $\tau_1=$ `dataL.coh.extension`, and let $\varphi$ be a class function on $L$ lying in the family `dataL.typeIHyp.Sset` with $\varphi(1)=[L:L_F]$ (where $L_F=$ `maxNilpotentNormalHall L`). Then, as class functions on $G$,
--
--   $$\varphi^{\tau_1}-\zeta_0^{\tau_1}=\beta_L^{\tau}(\zeta_0)-\beta_L^{\tau}(\varphi),$$
--
--   with $\beta_L^\tau=$ `typeIBetaL dataL.typeIHyp`.
--
--   This is the bridge allowing the $\zeta_0$-based parity argument of (13.19.c) to apply to an arbitrary degree-$e$ member $\varphi$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT.lean#L354-L410

import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem coh_extension_sub_zeta0_eq_typeIBetaL_sub [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ dataL.typeIHyp.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    dataL.coh.extension φ - dataL.coh.extension (dataL.zeta 0)
      = typeIBetaL dataL.typeIHyp (dataL.zeta 0) - typeIBetaL dataL.typeIHyp φ := by sorry

end OddOrder.Peterfalvi.S15
