-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_calT1_isCoherent
-- name    : OddOrder.Peterfalvi.S16.T_typeIII_calT1_isCoherent
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:05:05.19382+00:00
-- url     : https://prove2.me/theorems/fb6daa4d-2f2c-4276-9757-8a15dd435788
-- title:
--   Peterfalvi (14.9): the type-III family $\mathcal{T}_1$ is coherent with $\tau_T$ as Dade map
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, `hyp` a Peterfalvi §14 configuration with $T=$ `hyp.base.T`, assuming `Fintype G`, `Fintype T`, $T'=$ `(derivedInG T).subgroupOf T` finite, and $|G|,|T|,|T'|$ invertible in $\mathbb{C}$. Assume $T$ is of type III. Let $\mathcal{T}$ be a finite set of irreducible characters of $T'$ such that
--
--   - every $\theta\in\mathcal{T}$ has inertia group $T'$ in $T$;
--   - every $\theta\in\mathcal{T}$ is linear ($\theta(1)=1$) and nontrivial;
--   - $\mathcal{T}$ is closed under complex conjugation.
--
--   Let $S$ (`calT1_set`) be the set of class functions $\{\mathrm{Ind}_{T'}^{T}\theta:\theta\in\mathcal{T}\}$ and assume $|S|\ge 2$ (`2 ≤ S.ncard`). Then there exists a Peterfalvi §7 hypothesis `hyp07 : S07.Hypothesis S A₁(T)`, where $A_1(T)=$ `supportInSubgroup (sigmaSharp T) T`, whose Dade map `hyp07.tau` equals `tSideDadeMap hyp hG`, and such that $S$ is coherent with respect to it:
--   $$\texttt{Nonempty}\ \bigl(\texttt{S07.IsCoherent hyp07.tau}\ S\ A_1(T)\bigr).$$
--
--   The size bound $|S|\ge2$ is kept as an explicit hypothesis. The resulting coherent map $\tau_1$ feeds the (14.9) $\Gamma$-Bessel bound.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TTypeIICoherence.lean#L352-L470

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

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped Classical in

theorem T_typeIII_calT1_isCoherent [Finite G] (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hinertia : ∀ θ ∈ 𝒯,
      IrreducibleCharacter.inertia (G := ↥hyp.base.T)
          (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T)
    (hlinear : ∀ θ ∈ 𝒯, (θ.toClassFunction :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (hne : ∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter _)
    (hconj𝒯 : ∀ θ ∈ 𝒯,
      (⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
        θ.isIrreducible.conj⟩ :
        IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) ∈ 𝒯)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)))
    (hcard2 : 2 ≤ calT1_set.ncard) :
    ∃ hyp07 : OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.base.T) (G := G) calT1_set
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T),
      hyp07.tau = tSideDadeMap hyp hG ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp07.tau calT1_set
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)) := by sorry

end OddOrder.Peterfalvi.S16
