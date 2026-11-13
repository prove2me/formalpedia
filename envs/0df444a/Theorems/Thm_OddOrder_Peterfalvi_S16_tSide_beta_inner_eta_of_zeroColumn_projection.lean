-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_tSide_beta_inner_eta_of_zeroColumn_projection
-- name    : OddOrder.Peterfalvi.S16.tSide_beta_inner_eta_of_zeroColumn_projection
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:05:12.771732+00:00
-- url     : https://prove2.me/theorems/329de736-e4cf-476e-9b14-b6bb57848b83
-- title:
--   Peterfalvi (11.9)/(14.9): from the zero-column projection to $\langle b,\eta_{0j}\rangle=[j=0]$
-- statement:
--   Let $G$ be a finite group (with `Fintype G` and $|G|$ invertible in $\mathbb{C}$) and `base : S15.Hypothesis` a Peterfalvi §13 configuration for $G$ with primes $p,q$ and orthonormal $\eta$-grid $\eta_{ij}$ ($i<q$, $j<p$). Let $b$ be a complex class function on $G$ such that for every $j<p$,
--   $$\langle \eta_{0j},\,b\rangle \;=\; \Bigl\langle \eta_{0j},\ \sum_{i<q}\eta_{i0}\Bigr\rangle .$$
--   Then for every $j<p$,
--   $$\langle b,\,\eta_{0j}\rangle \;=\; \begin{cases}1 & j=0,\\ 0 & j\neq 0.\end{cases}$$
--
--   Here $b$ is intended to be the $T$-side Dade image of $\beta_{T,0}$; the hypothesis is the output of the projection calculation of (11.9). By orthonormality of the $\eta$-grid the right-hand inner product is $[j=0]$. This is the linear-algebraic passage from the deep projection statement to the orthogonality used in (14.9).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapCross.lean#L628-L682

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

namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped BigOperators

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem tSide_beta_inner_eta_of_zeroColumn_projection [Finite G]
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (b : ClassFunction G ℂ)
    (hproj : ∀ j : Fin base.p,
      ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j) b =
        ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j)
          (∑ i : Fin base.q,
            base.eta i ⟨0, base.p_prime.pos⟩))
    (j : Fin base.p) :
    ClassFunction.inner b (base.eta ⟨0, base.q_prime.pos⟩ j) =
      if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by sorry

end OddOrder.Peterfalvi.S16
