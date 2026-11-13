-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_etaGrid_zeroColumn_projection_of_coefficients_eq_column
-- name    : OddOrder.Peterfalvi.S16.etaGrid_zeroColumn_projection_of_coefficients_eq_column
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:07:03.863993+00:00
-- url     : https://prove2.me/theorems/03ed5088-e9d4-46bf-930d-34cf1d4316a7
-- title:
--   Peterfalvi (11.9)(a): coefficients equal to the zero column give the zero-column $\eta$-projection
-- statement:
--   Let $G$ be a finite group (with `Fintype G` and $|G|$ invertible in $\mathbb{C}$) and `base : S15.Hypothesis` a Peterfalvi §13 configuration with primes $p,q$ and $\eta$-grid. Let $b$ be a complex class function on $G$ and $m_{ij}\in\mathbb{Z}$ with $\langle b,\eta_{ij}\rangle=m_{ij}$ for all $i,j$. Assume the coefficients have the zero-column shape: $m_{ij}=1$ if $j=0$ and $m_{ij}=0$ otherwise. Then for every $j<p$,
--   $$\langle\eta_{0j},\,b\rangle \;=\;\Bigl\langle\eta_{0j},\ \sum_{i<q}\eta_{i0}\Bigr\rangle .$$
--
--   This is the linear-algebra bridge from the surviving coefficient alternative to the zero-column projection hypothesis of the (11.9)/(14.9) argument.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjectionRigidity.lean#L540-L590

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

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem etaGrid_zeroColumn_projection_of_coefficients_eq_column [Finite G]
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (b : ClassFunction G ℂ) (m : Fin base.q → Fin base.p → ℤ)
    (hm : ∀ i j, ClassFunction.inner b (base.eta i j) = (m i j : ℂ))
    (hcolumn : ∀ i j,
      m i j = if j = ⟨0, base.p_prime.pos⟩ then 1 else 0) :
    ∀ j : Fin base.p,
      ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j) b =
        ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j)
          (∑ i : Fin base.q, base.eta i ⟨0, base.p_prime.pos⟩) := by sorry

end OddOrder.Peterfalvi.S16
