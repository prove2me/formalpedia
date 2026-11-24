-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_Adapted_finrank_fil
-- name    : GlobalTheory.DRFil.Adapted.finrank_fil
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:35:59.234045+00:00
-- url     : https://prove2.me/theorems/18897d0f-696e-4d2b-bd82-562bdfc491fb
-- title:
--   Adapted: finrank fil
-- statement:
--   The Adapted construction uses the finrank fil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdemNotMemFilVOne.lean#L229-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdemNotMemFilVOne.lean#L229-L233

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

theorem GlobalTheory.DRFil.Adapted.finrank_fil (a : ℤ) :
    finrank LL ↥(FildR PD ρ τ a) = (Finset.univ.filter fun i => a ≤ k i).card := by sorry
