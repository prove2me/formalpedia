-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_exists_pu_field_repr
-- name    : OddOrder.Peterfalvi.S16.exists_pu_field_repr
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:19:27.916562+00:00
-- url     : https://prove2.me/theorems/53e44a53-98ad-4dfa-a06d-cca26d1f7d71
-- title:
--   Peterfalvi (14.2)(a)/(14.7): a field model $P\cong\mathbb{F}_{p^q}$ with $U\hookrightarrow\mathbb{F}^\times$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group and `hyp` a Peterfalvi §14 configuration with primes $p,q$ and subgroups $P,U$ of `hyp.base`. Assume $|U| = (p^q-1)/(p-1)$ (natural-number division). Then, writing $\mathbb{F}=\mathrm{GF}(p^q)$, there exist an additive isomorphism $e : P \cong \mathbb{F}$ (with $P$ written additively) and a group homomorphism $\mu : U \to \mathbb{F}^\times$ such that $\mu$ is injective and
--   $$e\bigl(vxv^{-1}\bigr) = \mu(v)\cdot e(x)\qquad(v\in U,\ x\in P).$$
--
--   (Here $vxv^{-1}\in P$ by `conj_mem_P`.) Thus $P$ becomes a one-dimensional $\mathbb{F}$-line on which $U$ acts through a faithful character.
--
--   This is the (14.2)(a) field model obtained from the §13 numerical data via the Singer mechanism; it uses that $P$ is elementary abelian of order $p^q$ and that $U$ acts faithfully on $P$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean#L679-L785

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
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas
import Definitions.Def_OddOrder_Peterfalvi_S07_CoherenceGalois
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_GaloisInnerTransport
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapGridAlignment
import Definitions.Def_OddOrder_Peterfalvi_S13_NonGaloisExclusion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped IsMulCommutative in

theorem exists_pu_field_repr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ (e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
      (μ : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ),
      Function.Injective μ ∧
      ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
        e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
            ↥hyp.base.P))
          = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x) := by sorry

end OddOrder.Peterfalvi.S16
