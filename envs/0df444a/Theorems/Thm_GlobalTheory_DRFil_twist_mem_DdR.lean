-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_twist_mem_DdR
-- name    : GlobalTheory.DRFil.twist_mem_DdR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:52.748847+00:00
-- url     : https://prove2.me/theorems/95709db5-ba79-45a7-bf52-b8b38ffd0fb0
-- title:
--   DRFil: twist mem Dd R
-- statement:
--   The DRFil construction uses the twist mem Dd R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdemNotMemFilVOne.lean#L88-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdemNotMemFilVOne.lean#L88-L99

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
variable (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V') (w : F) (ψ : G → Qp)
  (hw : ∀ g, PD.actdR g w = ψ g • w) (hf : ∀ g x, ψ g • ρ' g (f x) = f (ρ g x))
include hw hf

theorem GlobalTheory.DRFil.twist_mem_DdR {x : V ⊗[Qp] F} (hx : x ∈ DdR PD ρ) :
    mulR Qp F LL V' w (ext Qp F f x) ∈ DdR PD ρ' := by sorry
