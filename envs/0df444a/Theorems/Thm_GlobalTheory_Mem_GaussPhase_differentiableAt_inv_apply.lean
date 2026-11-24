-- Prove2me | Theorems.Thm_GlobalTheory_Mem_GaussPhase_differentiableAt_inv_apply
-- name    : GlobalTheory.Mem.GaussPhase.differentiableAt_inv_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:22:51.008084+00:00
-- url     : https://prove2.me/theorems/309f4865-639d-4eef-9579-1541756f81d5
-- title:
--   Gauss Phase: differentiable At inv apply
-- statement:
--   The Gauss Phase construction uses the differentiable At inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtInvApply.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtInvApply.lean#L22-L36

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

theorem GlobalTheory.Mem.GaussPhase.differentiableAt_inv_apply (M : ℝ → Matrix σ σ ℂ) (t : ℝ)
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) (hne : (M t).det ≠ 0) (i j : σ) :
    DifferentiableAt ℝ (fun s => (M s)⁻¹ i j) t := by sorry
