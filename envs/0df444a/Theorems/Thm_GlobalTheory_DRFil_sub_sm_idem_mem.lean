-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_sub_sm_idem_mem
-- name    : GlobalTheory.DRFil.sub_sm_idem_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:15.829116+00:00
-- url     : https://prove2.me/theorems/986150c4-097c-44a7-be8f-11c6515b3d27
-- title:
--   DRFil: sub sm idem mem
-- statement:
--   The DRFil construction uses the sub sm idem mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComponentEquiv.lean#L191-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComponentEquiv.lean#L191-L202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComponentEquiv
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

theorem GlobalTheory.DRFil.sub_sm_idem_mem (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) {y : V ⊗[Qp] F} (hy : y ∈ DdR PD ρ) :
    y - sm Qp F LL V (idem F τ) y ∈ Submodule.span LL
      {z | ∃ (c : K), ∃ y ∈ DdR PD ρ, z = mulR Qp F LL V (algebraMap K F c) y - τ c • y} := by sorry
