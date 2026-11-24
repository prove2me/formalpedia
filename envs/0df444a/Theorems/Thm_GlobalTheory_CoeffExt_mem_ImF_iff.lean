-- Prove2me | Theorems.Thm_GlobalTheory_CoeffExt_mem_ImF_iff
-- name    : GlobalTheory.CoeffExt.mem_ImF_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:15:18.961223+00:00
-- url     : https://prove2.me/theorems/9e235ae5-00ca-4db5-b426-3c065220fc35
-- title:
--   Coeff Ext: mem Im F iff
-- statement:
--   The Coeff Ext construction uses the mem Im F iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L424-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L424-L453

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

theorem GlobalTheory.CoeffExt.mem_ImF_iff (hE₁ : ∀ g x i, E₁ (ρ₁' g x) i = ρ₁ g (E₁ x i)) (hc₁ : Continuous E₁)
    (hs₁ : Continuous E₁.symm) (hL₁ : ∀ x, x ∈ L₁'.T ↔ ∀ i, E₁ x i ∈ L₁.T)
    (hE₂ : ∀ g x i, E₂ (ρ₂' g x) i = ρ₂ g (E₂ x i))
    (hL₂ : ∀ x, x ∈ L₂'.T ↔ ∀ i, E₂ x i ∈ L₂.T)
    (hF : ∀ x i, E₂ (F'.f x) i = F.f (E₁ x i)) (c : G → V₂') :
    c ∈ F'.ImF PD ↔ ∀ i, funCoord O G E₂ c i ∈ F.ImF PD := by sorry
