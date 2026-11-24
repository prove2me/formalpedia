-- Prove2me | Theorems.Thm_GlobalTheory_newton_step_root_in_disc
-- name    : GlobalTheory.newton_step_root_in_disc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:33.965771+00:00
-- url     : https://prove2.me/theorems/da3f1d7d-f34e-4089-ad28-727654b114b8
-- title:
--   Global Theory: newton step root in disc
-- statement:
--   The Global Theory construction uses the newton step root in disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NewtonPolygonLastDominantIndexMulXSubC.lean#L6-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NewtonPolygonLastDominantIndexMulXSubC.lean#L6-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NewtonPolygonLastDominantIndexMulXSubC
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

theorem GlobalTheory.newton_step_root_in_disc :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ),
      0 < ρ → ‖a‖ ≤ ρ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1)) ∧
        ∀ j, d + 1 < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j <
          ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) := by sorry
