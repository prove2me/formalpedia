-- Prove2me | Theorems.Thm_GlobalTheory_LocWeil_DerComm_quad_mem
-- name    : GlobalTheory.LocWeil.DerComm.quad_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:13:53.147909+00:00
-- url     : https://prove2.me/theorems/7cffa56b-a86e-468a-835a-ab10b1a8de4b
-- title:
--   Der Comm: quad mem
-- statement:
--   The Der Comm construction uses the quad mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtOneParameter.lean#L186-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtOneParameter.lean#L186-L187

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

theorem GlobalTheory.LocWeil.DerComm.quad_mem (b b' : ι → U) (Y : U →ₗ[ℝ] U) : quad d b b' Y ∈ Algebra.adjoin ℂ (Set.range d) := by sorry
