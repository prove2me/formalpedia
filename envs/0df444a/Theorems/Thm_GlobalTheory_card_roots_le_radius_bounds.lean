-- Prove2me | Theorems.Thm_GlobalTheory_card_roots_le_radius_bounds
-- name    : GlobalTheory.card_roots_le_radius_bounds
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:34.566706+00:00
-- url     : https://prove2.me/theorems/c2b43ff9-baaa-4e39-af3b-0fd0f886a1a4
-- title:
--   Global Theory: card roots le radius bounds
-- statement:
--   The Global Theory construction uses the card roots le radius bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardRootsClosedBallBoundsUltrametric.lean#L8-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardRootsClosedBallBoundsUltrametric.lean#L8-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallEqDominantIndexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
open GlobalTheory

theorem GlobalTheory.card_roots_le_radius_bounds :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ) (d : ℕ),
      0 < ρ → f.coeff d ≠ 0 →
      ((∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff d‖ * ρ ^ d) →
          d ≤ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧
      ((∀ j, d < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff d‖ * ρ ^ d) →
          Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) ≤ d) := by sorry
