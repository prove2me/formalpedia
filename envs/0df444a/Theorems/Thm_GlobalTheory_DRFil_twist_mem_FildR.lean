-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_twist_mem_FildR
-- name    : GlobalTheory.DRFil.twist_mem_FildR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:43.963395+00:00
-- url     : https://prove2.me/theorems/31f7f308-88d1-48ab-8aa6-01594cbad3c9
-- title:
--   DRFil: twist mem Fild R
-- statement:
--   The DRFil construction uses the twist mem Fild R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdemNotMemFilVOne.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdemNotMemFilVOne.lean#L101-L106

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

theorem GlobalTheory.DRFil.twist_mem_FildR (τ : K →ₐ[Qp] LL) {n a : ℤ} (hn : w ∈ PD.Fil n) {x : V ⊗[Qp] F}
    (hx : x ∈ FildR PD ρ τ a) : mulR Qp F LL V' w (ext Qp F f x) ∈ FildR PD ρ' τ (n + a) := by sorry
