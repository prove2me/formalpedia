-- Prove2me | Theorems.Thm_GlobalTheory_Mem_GaussPhase_hasDerivAt_phase
-- name    : GlobalTheory.Mem.GaussPhase.hasDerivAt_phase
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:08.60306+00:00
-- url     : https://prove2.me/theorems/e88709a5-b829-4dd6-8dc0-c48b34832ea9
-- title:
--   Gauss Phase: has Deriv At phase
-- statement:
--   The Gauss Phase construction uses the has Deriv At phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtInvApply.lean#L54-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtInvApply.lean#L54-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtInvApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GaussPhase
variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem GlobalTheory.Mem.GaussPhase.hasDerivAt_phase (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ)
    (x y : σ → ℂ) (t : ℝ) (hS : Sᵀ = S) (hT : Tᵀ = T)
    (hu : IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det) :
    let w : ℝ → σ → ℂ := fun s => (1 - ((s : ℂ) ^ 2) • (T * S))⁻¹ *ᵥ (y + (s : ℂ) • T *ᵥ x)
    let u : ℝ → σ → ℂ := fun s => x + (s : ℂ) • S *ᵥ w s
    HasDerivAt (fun s : ℝ => (s : ℂ) / 2 * (x ⬝ᵥ w s + y ⬝ᵥ u s)) (u t ⬝ᵥ w t) t := by sorry
