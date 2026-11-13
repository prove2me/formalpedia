-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_exists_zeta_index_of_mem_Sset
-- name    : OddOrder.Peterfalvi.S15.exists_zeta_index_of_mem_Sset
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:26:29.331247+00:00
-- url     : https://prove2.me/theorems/cf2ef388-3147-437e-a8fa-045576484de1
-- title:
--   Every member of the type I family is an enumerated $\zeta_k$ with $k\ne$ `ind1H`
-- statement:
--   Let $G$ be a finite group with `IsMinimalSimpleOdd G`, let $L\le G$ carry `dataL : TypeICoherent78Data L`, with enumerated characters $\zeta_0,\dots,\zeta_n$ (`dataL.zeta`, $n=$ `dataL.n`) and distinguished index `dataL.ind1H`, and let $\varphi$ be a class function on $L$ lying in `dataL.typeIHyp.Sset`. Then there is an index $k\in\{0,\dots,n\}$ with $k\ne$ `dataL.ind1H` and
--
--   $$\zeta_k=\varphi .$$
--
--   This is the converse of `TypeICoherent78Data.zeta_mem_Sset`; the exclusion of `ind1H` uses that $\mathrm{Ind}\,1_H$ is real while a nontrivial induced irreducible is not, by oddness of the order.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTGrid.lean#L605-L664

import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
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

theorem exists_zeta_index_of_mem_Sset [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ dataL.typeIHyp.Sset) :
    ∃ k : Fin (dataL.n + 1), k ≠ dataL.ind1H ∧ dataL.zeta k = φ := by sorry

end OddOrder.Peterfalvi.S15
