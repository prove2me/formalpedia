-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_field_repr_rescale_to_W2
-- name    : OddOrder.Peterfalvi.S16.field_repr_rescale_to_W2
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:18:24.392089+00:00
-- url     : https://prove2.me/theorems/b91cc503-8e5f-4794-8b2b-2ec17a28aa3b
-- title:
--   Peterfalvi (14.7): rescaling a field model of $P$ so that the prime line corresponds to $W_2$
-- statement:
--   Let `hyp` be a Peterfalvi §14 configuration with primes $p,q$ and subgroups $P,U,W_2$ of `hyp.base`, with $W_2\le P$. Let $\mathbb{F}=\mathrm{GF}(p^q)$. Let $e_0 : P\cong \mathbb{F}$ be an additive isomorphism and $\mu : U\to\mathbb{F}^\times$ a homomorphism with
--   $$e_0(vxv^{-1}) = \mu(v)\,e_0(x)\qquad(v\in U,\ x\in P).$$
--   Then there exists an additive isomorphism $e : P\cong\mathbb{F}$ with the same compatibility $e(vxv^{-1})=\mu(v)e(x)$ and such that the image of the $\mathbb{F}_p$-span of $\{1\}\subset\mathbb{F}$ under `fieldNormalizerKernelTransport hyp e` is exactly $W_2$.
--
--   The model is rescaled by a nonzero field scalar: $e = e_0(w_0)^{-1}\cdot e_0$ for a nonidentity $w_0\in W_2$. Since $\mathbb{F}$ is commutative, compatibility is preserved. This produces the prime-line input of (14.7).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean#L844-L955

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

theorem field_repr_rescale_to_W2 (hyp : Hypothesis (G := G))
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P)
    (e₀ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hcompat₀ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
           e₀ (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
               ↥hyp.base.P))
             = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                 GaloisField hyp.base.p hyp.base.q) * e₀ (Additive.ofMul x)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q,
      (∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
              ↥hyp.base.P))
            = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x)) ∧
      (((Submodule.span (ZMod hyp.base.p)
            ({(1 : GaloisField hyp.base.p hyp.base.q)} :
              Set (GaloisField hyp.base.p hyp.base.q))).toAddSubgroup).toSubgroup).map
          (fieldNormalizerKernelTransport hyp e) = hyp.base.W2 := by sorry

end OddOrder.Peterfalvi.S16
