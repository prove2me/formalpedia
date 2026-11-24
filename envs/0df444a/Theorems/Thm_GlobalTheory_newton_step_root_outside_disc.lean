-- Prove2me | Theorems.Thm_GlobalTheory_newton_step_root_outside_disc
-- name    : GlobalTheory.newton_step_root_outside_disc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:23.845913+00:00
-- url     : https://prove2.me/theorems/70cdc6a3-d14c-4a58-be86-5fa8648f9f3a
-- title:
--   Global Theory: newton step root outside disc
-- statement:
--   The Global Theory construction uses the newton step root outside disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NewtonPolygonDominantIndexXSubCMul.lean#L19-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NewtonPolygonDominantIndexXSubCMul.lean#L19-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NewtonPolygonDominantIndexXSubCMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.newton_step_root_outside_disc :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ρ < ‖a‖ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d) ∧ ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff d‖ * ρ ^ d := by sorry
