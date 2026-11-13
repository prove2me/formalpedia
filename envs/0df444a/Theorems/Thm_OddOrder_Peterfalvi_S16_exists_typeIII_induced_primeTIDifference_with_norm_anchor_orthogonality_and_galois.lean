-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_exists_typeIII_induced_primeTIDifference_with_norm_anchor_orthogonality_and_galois
-- name    : OddOrder.Peterfalvi.S16.exists_typeIII_induced_primeTIDifference_with_norm_anchor_orthogonality_and_galois
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:33:53.959561+00:00
-- url     : https://prove2.me/theorems/04409de8-ad33-42b8-ba2b-9643609055d6
-- title:
--   Peterfalvi (11.9)(a): normed prime-TI difference with anchor orthogonality, reality and Galois invariance
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, `hyp` a Peterfalvi §14 configuration with $p=$ `hyp.base.p`, $T=$ `hyp.base.T`, and let $T'=$ the derived subgroup of $T$ taken as a subgroup of $T$ (`(derivedInG T).subgroupOf T`); the usual `Fintype`/`Invertible` instances for $G,T,T'$ are assumed. Assume $T$ is of type III. Let $\theta$ be a nontrivial irreducible character of $T'$ such that $\zeta:=\mathrm{Ind}_{T'}^{T}\theta$ is an irreducible character of $T$ with $\zeta(1)=p$. Then there exists a class function $\nu_0$ on $T$ such that, with $\tau_T=$ `tSideDadeMap hyp hG`, $A_1(T)=$ `supportInSubgroup (sigmaSharp T) T`:
--
--   1. $\nu_0\in\mathrm{ZIrr}(T)$ and $\nu_0$ is real;
--   2. $\nu_0-\zeta\in\mathrm{ZIrr}(T)$ and its support lies in $A_1(T)$;
--   3. $\tau_T(\nu_0-\zeta)\in\mathrm{ZIrr}(G)$ and $\tau_T(\nu_0-\zeta)(1)=0$;
--   4. $\overline{\nu_0-\zeta}=\nu_0-\bar\zeta$;
--   5. $\langle\nu_0,1_T\rangle=1$, $\langle\nu_0,\zeta\rangle=0$, $\langle\nu_0,\bar\zeta\rangle=0$;
--   6. $\langle\nu_0-\zeta,\nu_0-\zeta\rangle=p+1$ and $\langle\tau_T(\nu_0-\zeta),\tau_T(\nu_0-\zeta)\rangle=p+1$;
--   7. $\nu_0$ is fixed by every field automorphism $\sigma$ of $\mathbb{C}$ acting on class functions (`mapRingEquiv σ ν0 = ν0`);
--   8. $\nu_0=\mathrm{Ind}_{T'}^{T}(1_{T'})$.
--
--   This is the normed bridge of (11.9)(a) in a projection-ready form that retains the orthogonality of the canonical prime-TI anchor $\nu_0$ to the induced source $\zeta$ and its conjugate.
--
--   **Formalization Note.** `trivialIrreducibleCharacter`/`trivialClassFunction` denote the trivial character; `ZIrr` is the $\mathbb{Z}$-span of the irreducible characters; the conclusion is a single existential over $\nu_0$ with a conjunction of conditions, grouped in the list above.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapPrimeTI.lean#L681-L845

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

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in

theorem exists_typeIII_induced_primeTIDifference_with_norm_anchor_orthogonality_and_galois
    [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G]
    [fintypeT : Fintype ↥hyp.base.T]
    [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    [invertibleT : Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [invertibleK :
      Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (θ : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T))
    (hθne : θ ≠ trivialIrreducibleCharacter _)
    (hζirr : IsIrreducibleCharacter
      (ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))
    (hζ1 : ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction 1 =
        (hyp.base.p : ℂ)) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)
            ∈ ZIrr ↥hyp.base.T ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup
            (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ∧
        tSideDadeMap hyp hG
          (ν0 - ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) ∈ ZIrr G ∧
        tSideDadeMap hyp hG
          (ν0 - ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) 1 = 0 ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj =
            ν0 - (ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 ∧
        ClassFunction.inner ν0
          (ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) = 0 ∧
        ClassFunction.inner ν0
          (ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj = 0 ∧
        ClassFunction.inner
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) =
          ((hyp.base.p : ℕ) + 1 : ℂ) ∧
        ClassFunction.inner
            (tSideDadeMap hyp hG
              (ν0 - ClassFunction.induce
                ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))
            (tSideDadeMap hyp hG
              (ν0 - ClassFunction.induce
                ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)) =
          ((hyp.base.p : ℕ) + 1 : ℂ) ∧
        (∀ sigma : ℂ ≃+* ℂ,
          ClassFunction.mapRingEquiv sigma ν0 = ν0) ∧
        ν0 = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (trivialClassFunction
            ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) := by sorry

end OddOrder.Peterfalvi.S16
