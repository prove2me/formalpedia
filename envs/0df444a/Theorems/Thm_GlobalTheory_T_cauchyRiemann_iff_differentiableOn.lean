-- Prove2me | Theorems.Thm_GlobalTheory_T_cauchyRiemann_iff_differentiableOn
-- name    : GlobalTheory.T.cauchyRiemann_iff_differentiableOn
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:36.396807+00:00
-- url     : https://prove2.me/theorems/5466ad58-dc3c-4c39-ac89-09d79717705a
-- title:
--   T: cauchy Riemann iff differentiable On
-- statement:
--   The T construction uses the cauchy Riemann iff differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CauchyRiemannIffDifferentiableOnComplexStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CauchyRiemannIffDifferentiableOnComplexStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplexStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real

theorem GlobalTheory.T.cauchyRiemann_iff_differentiableOn : ∀ (g : ℕ) (U : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℂ), IsOpen U → (DifferentiableOn ℝ f U → ((∀ a, ∀ z ∈ U, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = 0) ↔ DifferentiableOn ℂ f U)) ∧ (DifferentiableOn ℂ f U → ContDiffOn ℝ ∞ f U ∧ ∀ v, DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U) := by sorry
