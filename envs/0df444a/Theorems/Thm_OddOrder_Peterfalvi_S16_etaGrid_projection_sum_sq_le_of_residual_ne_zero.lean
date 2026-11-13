-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_etaGrid_projection_sum_sq_le_of_residual_ne_zero
-- name    : OddOrder.Peterfalvi.S16.etaGrid_projection_sum_sq_le_of_residual_ne_zero
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:07:32.110572+00:00
-- url     : https://prove2.me/theorems/4465bd24-4493-4714-9b78-70f24224d43b
-- title:
--   Peterfalvi (11.9)(a): a nonzero residual sharpens the projection bound to $\sum m_{ij}^2\le p$
-- statement:
--   Let $G$ be a finite group (with `Fintype G` and $|G|$ invertible in $\mathbb{C}$) and `base : S15.Hypothesis` a Peterfalvi §13 configuration with primes $p,q$ and $\eta$-grid. Let $b\in\mathrm{ZIrr}(G)$ with $\langle b,b\rangle=p+1$, and let $m_{ij}\in\mathbb{Z}$ with $\langle b,\eta_{ij}\rangle=m_{ij}$ for all $i<q$, $j<p$. If the perpendicular residual $b-\sum m_{ij}\eta_{ij}$ (`b - etaGridProjection base m`) is nonzero, then
--   $$\sum_{i<q}\sum_{j<p}m_{ij}^2\;\le\;p .$$
--
--   A nonzero residual is a nonzero virtual character, hence has integral squared norm at least $1$; Pythagoras then sharpens $\sum m_{ij}^2\le p+1$ to $\le p$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjection.lean#L115-L166

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PrimeTIResidue
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S13_Orthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity

namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in

theorem etaGrid_projection_sum_sq_le_of_residual_ne_zero [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    {b : ClassFunction G ℂ} (hbZ : b ∈ ZIrr G)
    (hbnorm : ClassFunction.inner b b = (((base.p : ℤ) + 1) : ℂ))
    (m : Fin base.q → Fin base.p → ℤ)
    (hcoeff : ∀ i j, ClassFunction.inner b (base.eta i j) = (m i j : ℂ))
    (hresidual : b - etaGridProjection base m ≠ 0) :
    (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤ (base.p : ℤ) := by sorry

end OddOrder.Peterfalvi.S16
