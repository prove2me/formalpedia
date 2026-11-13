-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_exists_etaGrid_intProjection_of_inner_self_eq
-- name    : OddOrder.Peterfalvi.S16.exists_etaGrid_intProjection_of_inner_self_eq
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:07:45.128203+00:00
-- url     : https://prove2.me/theorems/2b3f95e4-3c22-4c17-a229-837913f4329d
-- title:
--   Peterfalvi (11.9)(a): integral $\eta$-grid projection of a virtual character of norm $p+1$, with $\sum m_{ij}^2\le p+1$
-- statement:
--   Let $G$ be a finite group (with `Fintype G` and $|G|$ invertible in $\mathbb{C}$) and `base : S15.Hypothesis` a Peterfalvi §13 configuration with primes $p,q$ and orthonormal $\eta$-grid. Let $b\in\mathrm{ZIrr}(G)$ with $\langle b,b\rangle=p+1$. Then there are integers $m_{ij}$ ($i<q$, $j<p$) such that
--
--   - $\langle b,\eta_{ij}\rangle=m_{ij}$ for all $i,j$;
--   - $\langle b,b\rangle=\sum_{i,j}m_{ij}^2+\langle b-X,\ b-X\rangle$, where $X=\sum m_{ij}\eta_{ij}$ (`etaGridProjection base m`);
--   - $\sum_{i<q}\sum_{j<p} m_{ij}^2\le p+1$.
--
--   The coefficients are integers because $b$ is a virtual character and the $\eta_{ij}$ are characters or negatives thereof; the Pythagorean identity then bounds the sum of squares. In the $T$-side bridge, $b=\tau_T(\nu_0-\zeta)$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjection.lean#L25-L77

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

theorem exists_etaGrid_intProjection_of_inner_self_eq [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    {b : ClassFunction G ℂ} (hbZ : b ∈ ZIrr G)
    (hbnorm : ClassFunction.inner b b = (((base.p : ℤ) + 1) : ℂ)) :
    ∃ m : Fin base.q → Fin base.p → ℤ,
      (∀ i j, ClassFunction.inner b (base.eta i j) = (m i j : ℂ)) ∧
      ClassFunction.inner b b =
        ((∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) : ℂ) +
          ClassFunction.inner (b - etaGridProjection base m)
            (b - etaGridProjection base m) ∧
      (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤
        (base.p : ℤ) + 1 := by sorry

end OddOrder.Peterfalvi.S16
