-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_Adapted_tensor
-- name    : GlobalTheory.DRFil.Adapted.tensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:30.376473+00:00
-- url     : https://prove2.me/theorems/8fbae019-5841-4843-9021-3989d5824b49
-- title:
--   Adapted: tensor
-- statement:
--   The Adapted construction uses the tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdemNotMemFilVOne.lean#L279-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdemNotMemFilVOne.lean#L279-L334

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
variable [FiniteDimensional Qp K] [CharZero Qp]
open GlobalTheory.DRFil.Adapted
variable {PD} {ρ : Representation LL G V} {τ : K →ₐ[Qp] LL} {ι : Type} [Fintype ι]
    {d : ι → V ⊗[Qp] F} {k : ι → ℤ} (h : Adapted PD ρ τ d k)
include h

theorem GlobalTheory.DRFil.Adapted.tensor {ρ' : Representation LL G V'} {ι' : Type} [Fintype ι'] {d' : ι' → V' ⊗[Qp] F} {k' : ι' → ℤ}
    (h' : Adapted PD ρ' τ d' k') (ρ'' : Representation LL G V'') (E : V ⊗[LL] V' ≃ₗ[LL] V'')
    (hE : ∀ g x y, ρ'' g (E (x ⊗ₜ[LL] y)) = E (ρ g x ⊗ₜ[LL] ρ' g y)) :
    Adapted PD ρ'' τ (fun p : ι × ι' => bil Qp F (tensBil E) (d p.1) (d' p.2)) fun p => k p.1 + k' p.2 := by sorry
