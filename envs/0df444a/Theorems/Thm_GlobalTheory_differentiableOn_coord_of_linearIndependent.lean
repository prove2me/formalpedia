-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_coord_of_linearIndependent
-- name    : GlobalTheory.differentiableOn_coord_of_linearIndependent
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:42:04.886739+00:00
-- url     : https://prove2.me/theorems/f4132073-365a-4974-be03-318f7d04d7bb
-- title:
--   Global Theory: differentiable On coord of linear Independent
-- statement:
--   The Global Theory construction uses the differentiable On coord of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DifferentiableOnCoordOfLinearIndependent.lean#L15-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DifferentiableOnCoordOfLinearIndependent.lean#L15-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DifferentiableOnCoordOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Filter Topology

theorem GlobalTheory.differentiableOn_coord_of_linearIndependent :
    ∀ (E Z I : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype I] (W : Set E) (Th : I → E → Z → ℂ) (F : E → Z → ℂ) (c : E → I → ℂ), IsOpen W → (∀ k z, DifferentiableOn ℂ (fun e => Th k e z) W) → (∀ z, DifferentiableOn ℂ (fun e => F e z) W) → (∀ e ∈ W, LinearIndependent ℂ (fun k => Th k e)) → (∀ e ∈ W, ∀ z, F e z = ∑ k, c e k * Th k e z) → ∀ k, DifferentiableOn ℂ (fun e => c e k) W := by sorry
