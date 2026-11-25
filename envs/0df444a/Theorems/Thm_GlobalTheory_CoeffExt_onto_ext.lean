-- Prove2me | Theorems.Thm_GlobalTheory_CoeffExt_onto_ext
-- name    : GlobalTheory.CoeffExt.onto_ext
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:59:04.157533+00:00
-- url     : https://prove2.me/theorems/265cfc08-91fe-4fd2-9cf1-7767a5d8485c
-- title:
--   Coeff Ext: onto ext
-- statement:
--   The Coeff Ext construction uses the onto ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L459-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L459-L469

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']
    {O O' : Type} [CommRing O] [CommRing O'] [Algebra O LL] [Algebra O' LL']
    {ι : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace G]
variable {V₁ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [Module O V₁] [IsScalarTower O LL V₁]
    [TopologicalSpace V₁] [ContinuousAdd V₁] [ContinuousConstSMul LL V₁]
    {V₁' : Type} [AddCommGroup V₁'] [Module LL V₁'] [Module Qp V₁'] [IsScalarTower Qp LL V₁']
    [Module LL' V₁'] [IsScalarTower Qp LL' V₁'] [Module O V₁'] [IsScalarTower O LL V₁']
    [Module O' V₁'] [IsScalarTower O' LL' V₁']
    [TopologicalSpace V₁'] [ContinuousAdd V₁'] [ContinuousConstSMul LL' V₁']
    {ρ₁ : Representation LL G V₁} {ρ₁' : Representation LL' G V₁'}
    {E₁ : V₁' ≃ₗ[LL] (ι → V₁)} {L₁ : Lattice (O := O) ρ₁} {L₁' : Lattice (O := O') ρ₁'}
    {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [Module O V₂] [IsScalarTower O LL V₂]
    [TopologicalSpace V₂] [ContinuousAdd V₂] [ContinuousConstSMul LL V₂]
    {V₂' : Type} [AddCommGroup V₂'] [Module LL V₂'] [Module Qp V₂'] [IsScalarTower Qp LL V₂']
    [Module LL' V₂'] [IsScalarTower Qp LL' V₂'] [Module O V₂'] [IsScalarTower O LL V₂']
    [Module O' V₂'] [IsScalarTower O' LL' V₂']
    [TopologicalSpace V₂'] [ContinuousAdd V₂'] [ContinuousConstSMul LL' V₂']
    {ρ₂ : Representation LL G V₂} {ρ₂' : Representation LL' G V₂'}
    {E₂ : V₂' ≃ₗ[LL] (ι → V₂)} {L₂ : Lattice (O := O) ρ₂} {L₂' : Lattice (O := O') ρ₂'}
    (F : LatHom L₁ L₂) (F' : LatHom L₁' L₂')
omit [TopologicalSpace G] [Fintype ι] [DecidableEq ι] [ContinuousAdd V₁] [ContinuousConstSMul LL V₁]
  [ContinuousAdd V₁'] [ContinuousConstSMul LL' V₁'] [ContinuousAdd V₂] [ContinuousConstSMul LL V₂]
  [ContinuousAdd V₂'] [ContinuousConstSMul LL' V₂'] [Module O V₁'] [IsScalarTower O LL V₁']
  [Module O V₂'] [IsScalarTower O LL V₂']

theorem GlobalTheory.CoeffExt.onto_ext (hL₁ : ∀ x, x ∈ L₁'.T ↔ ∀ i, E₁ x i ∈ L₁.T)
    (hL₂ : ∀ x, x ∈ L₂'.T ↔ ∀ i, E₂ x i ∈ L₂.T)
    (hF : ∀ x i, E₂ (F'.f x) i = F.f (E₁ x i)) (h : F.Onto) : F'.Onto := by sorry
