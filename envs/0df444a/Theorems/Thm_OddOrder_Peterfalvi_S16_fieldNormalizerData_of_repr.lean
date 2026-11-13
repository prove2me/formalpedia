-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_fieldNormalizerData_of_repr
-- name    : OddOrder.Peterfalvi.S16.fieldNormalizerData_of_repr
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:21:48.820758+00:00
-- url     : https://prove2.me/theorems/c65a5441-3e12-48fb-8b53-4f1ed43af87a
-- title:
--   Peterfalvi (14.7): existence of `FieldNormalizerData` from a field model of $P$ with $U$-action
-- statement:
--   Let `hyp` be a Peterfalvi §14 configuration with primes $p,q$ and subgroups $P, U, Q, W_2$ of `hyp.base`; write $\mathbb{F}=\mathrm{GF}(p^q)$ (`GaloisField p q`). Suppose we are given:
--
--   - an additive isomorphism $e : P \cong \mathbb{F}$ (writing $P$ additively);
--   - an injective homomorphism $\mu : U\to\mathbb{F}^\times$ whose range is the norm-one units `AppC.NormSet.normOneUnits p q`;
--   - $U$ normalizes $P$: $vxv^{-1}\in P$ for $v\in U$, $x\in P$ (`hUP`);
--   - compatibility $e(vxv^{-1}) = \mu(v)\,e(x)$ for all $v\in U$, $x\in P$;
--   - the prime-line identification: the image of the $\mathbb{F}_p$-span of $1\in\mathbb{F}$ under `fieldNormalizerKernelTransport hyp e` equals $W_2$;
--   - $P\cap U = 1$;
--   - $\gcd\bigl((p^q-1)/(p-1),\,p-1\bigr)=1$;
--   - $Q$ is elementary abelian of exponent $q$ (`IsElementaryAbelian q Q`);
--   - $W_2$ normalizes $Q$;
--   - some $y_Q\in Q$ with $y_Q W_2 y_Q^{-1}$ (as `MulAut.conj yQ • W2`) contained in $N_G(U)$.
--
--   Then `FieldNormalizerData hyp` is nonempty.
--
--   This is the ungated reduction at the heart of (14.7): the embedding $\sigma$ is built as a `SemidirectProduct.lift` of two transport homomorphisms, glued by the (14.2)(a) field model. All hypotheses are inputs; no §13 character theory is invoked.
--
--   **Formalization Note.** `Fact p.Prime` instances are introduced via `letI`; $P$ is regarded as `Additive ↥P`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean#L454-L633

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

set_option backward.isDefEq.respectTransparency false in

theorem fieldNormalizerData_of_repr (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q)
    (hUP : ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
         (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.base.P)
    (hcompat : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
           e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hUP v x⟩ : ↥hyp.base.P))
             = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                 GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x))
    (hW2 : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         (((Submodule.span (ZMod hyp.base.p)
             ({(1 : GaloisField hyp.base.p hyp.base.q)} :
               Set (GaloisField hyp.base.p hyp.base.q))).toAddSubgroup).toSubgroup).map
           (fieldNormalizerKernelTransport hyp e) = hyp.base.W2)
    (hPU_disj : hyp.base.P ⊓ hyp.base.U = ⊥)
    (hcyclotomic :
       Nat.Coprime ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) (hyp.base.p - 1))
    (hQ_elemAb : IsElementaryAbelian hyp.base.q ↥hyp.base.Q)
    (hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G))
    (yQ : G) (hyQ_mem : yQ ∈ hyp.base.Q)
    (hW2_conj_y : MulAut.conj yQ • hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G)) :
    Nonempty (FieldNormalizerData hyp) := by sorry

end OddOrder.Peterfalvi.S16
