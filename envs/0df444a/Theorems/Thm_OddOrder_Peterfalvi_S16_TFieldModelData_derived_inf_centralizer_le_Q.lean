-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_TFieldModelData_derived_inf_centralizer_le_Q
-- name    : OddOrder.Peterfalvi.S16.TFieldModelData.derived_inf_centralizer_le_Q
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:30:42.038206+00:00
-- url     : https://prove2.me/theorems/f2a13df0-01ef-436d-b5fd-071d3a9bbb45
-- title:
--   Peterfalvi (14.4)/(13.12) dual: $C_{T'}(x)\le Q$ for $x\in Q^\#$ from the $T$-side field model
-- statement:
--   Let $G$ be a finite group, `hyp` a Peterfalvi §13 configuration for $G$ (subgroups $T, Q$), and `data : TFieldModelData hyp` the $T$-side field-model data (the (14.4) carrier). Then for every $x\in Q^\#$ (`x ∈ sharpSubgroup hyp.Q`, a nonidentity element of $Q$),
--   $$T' \cap C_G(x) \;\le\; Q,$$
--   where $T'$ is the derived subgroup of $T$ taken in $G$ (`derivedInG hyp.T`).
--
--   This is the Frobenius-kernel property of $T' = QV$, transported from the field model. It discharges the `hfrobT` hypothesis of the $T$-side order-coprimality statement once the (14.4) carrier is available.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_G0Coprime.lean#L814-L853

import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas
import Definitions.Def_OddOrder_GroupTheory_ConjClassSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_G0Coprime

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

theorem TFieldModelData.derived_inf_centralizer_le_Q [Finite G]
    {hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)} (data : TFieldModelData hyp)
    {x : G} (hx : x ∈ sharpSubgroup hyp.Q) :
    derivedInG hyp.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.Q := by sorry

end OddOrder.Peterfalvi.S16
