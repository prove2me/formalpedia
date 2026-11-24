-- Prove2me | Theorems.Thm_GlobalTheory_CoeffExt_mem_B1T_iff
-- name    : GlobalTheory.CoeffExt.mem_B1T_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:15:15.541299+00:00
-- url     : https://prove2.me/theorems/4635675d-6cf0-4890-aa07-1549698e4b56
-- title:
--   Coeff Ext: mem B1 T iff
-- statement:
--   The Coeff Ext construction uses the mem B1 T iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L380-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L380-L398

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
variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [Module O V'] [IsScalarTower O LL V']
    [Module O' V'] [IsScalarTower O' LL' V']
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {E : V' ≃ₗ[LL] (ι → V)} {L : Lattice (O := O) ρ} {L' : Lattice (O := O') ρ'}
omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
  [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL' V'] [Fintype ι]
  [DecidableEq ι]

theorem GlobalTheory.CoeffExt.mem_B1T_iff (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
    (hL : ∀ x, x ∈ L'.T ↔ ∀ i, E x i ∈ L.T) (c : G → V') :
    c ∈ latticeCoboundaries L' ↔ ∀ i, funCoord O G E c i ∈ latticeCoboundaries L := by sorry
