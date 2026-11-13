-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_calT1_family_galois
-- name    : OddOrder.Peterfalvi.S16.T_typeIII_calT1_family_galois
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:34:58.762403+00:00
-- url     : https://prove2.me/theorems/bdbd02fa-59e4-4630-adf9-fdbef76e7c90
-- title:
--   Peterfalvi (14.9): the family $\mathcal{T}\subseteq\mathrm{Irr}(QV)$: inertia, linearity, conjugation, Galois closure
-- statement:
--   Let `hyp` be a Peterfalvi §14 configuration for a finite group $G$ with $T=$ `hyp.base.T`, primes $p,q$, and $V=$ `hyp.base.V`; let $T'$ be the derived subgroup of $T$ regarded inside $T$ (`(derivedInG T).subgroupOf T`), with the usual instances (`Fintype T`, $T'$ finite, $|T|$ and $|T'|$ invertible in $\mathbb{C}$). Let `td : TypeIIIData T` be type-III structure data for $T$. Then there is a finite set $\mathcal{T}$ of irreducible characters of $T'$ such that
--
--   - every $\theta\in\mathcal{T}$ has inertia group $I_T(\theta)=T'$;
--   - every $\theta\in\mathcal{T}$ is nontrivial;
--   - every $\theta\in\mathcal{T}$ is linear: $\theta(1)=1$;
--   - $\mathcal{T}$ is closed under complex conjugation;
--   - $\mathcal{T}$ is closed under every field automorphism $\sigma$ of $\mathbb{C}$ (`IrreducibleCharacter.galoisMap σ θ`);
--   - the set of induced characters $\{\mathrm{Ind}_{T'}^{T}\theta:\theta\in\mathcal{T}\}$ has cardinality
--   $$\frac{|V|-1}{p}$$
--   (natural-number division, $|V|$ = `Nat.card hyp.base.V`).
--
--   This constructs the inflated $\mathrm{Irr}(QV/Q)$-family $\mathcal{T}$ with all the predicates consumed by the (14.9) coherence assembler.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean#L679-L915

import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroupQuotient
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_OrbitOnIrr
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas
import Definitions.Def_OddOrder_Peterfalvi_S16_G0Coprime
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped IsMulCommutative in
open scoped Classical in

theorem T_typeIII_calT1_family_galois [Finite G] (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (td : TypeIIIData hyp.base.T) :
    ∃ 𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)),
      (∀ θ ∈ 𝒯,
        IrreducibleCharacter.inertia (G := ↥hyp.base.T)
            (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
          = (derivedInG hyp.base.T).subgroupOf hyp.base.T) ∧
      (∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter _) ∧
      (∀ θ ∈ 𝒯, (θ.toClassFunction :
        ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1) ∧
      (∀ θ ∈ 𝒯,
        (⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
          θ.isIrreducible.conj⟩ :
          IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) ∈ 𝒯) ∧
      (∀ (σc : ℂ ≃+* ℂ) θ, θ ∈ 𝒯 →
        IrreducibleCharacter.galoisMap σc θ ∈ 𝒯) ∧
      (𝒯.image (fun θ => ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)).card
        = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by sorry

end OddOrder.Peterfalvi.S16
