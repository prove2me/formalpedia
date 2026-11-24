-- Prove2me | Theorems.Thm_GlobalTheory_LocWeil_DerComm_DualBases_quad_lie
-- name    : GlobalTheory.LocWeil.DerComm.DualBases.quad_lie
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:13:52.522741+00:00
-- url     : https://prove2.me/theorems/82248881-b1bb-4074-a838-4cc9e9b30bac
-- title:
--   Dual Bases: quad lie
-- statement:
--   The Dual Bases construction uses the quad lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtOneParameter.lean#L215-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtOneParameter.lean#L215-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.LocWeil GlobalTheory.LocWeil.DerComm
variable {S U : Type} [AddCommGroup S] [Module ℂ S]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable (β : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) {ι : Type} [Fintype ι] (b b' : ι → U)
variable {β b b'}
variable {d : U →ₗ[ℝ] Module.End ℂ S} {κ : ℂ} {Y : U →ₗ[ℝ] U}

theorem GlobalTheory.LocWeil.DerComm.DualBases.quad_lie (h : DualBases β b b') {N : Submodule ℂ S} (hN : ∀ u, ∀ Φ ∈ N, d u Φ ∈ N)
    (A : Module.End ℂ S) (Z : U →ₗ[ℝ] U) (hA : ∀ u, ∀ Φ ∈ N, A (d u Φ) = d (Z u) Φ + d u (A Φ))
    (hZ : ∀ x y, β (Z x) y = -β x (Z y)) (hc : ∀ x, Z (Y x) = Y (Z x)) :
    ∀ Φ ∈ N, A (quad d b b' Y Φ) = quad d b b' Y (A Φ) := by sorry
