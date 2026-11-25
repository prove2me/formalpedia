-- Prove2me | Theorems.Thm_GlobalTheory_T_card_roots_closedBall_bounds_ultrametric
-- name    : GlobalTheory.T.card_roots_closedBall_bounds_ultrametric
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:44.186307+00:00
-- url     : https://prove2.me/theorems/83f5d723-314e-4de5-a04d-f585cf71731c
-- title:
--   T: card roots closed Ball bounds ultrametric
-- statement:
--   The T construction uses the card roots closed Ball bounds ultrametric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardRootsClosedBallBoundsUltrametricStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardRootsClosedBallBoundsUltrametricStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametric
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametricStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_roots_closedBall_bounds_ultrametric : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ) (d : ℕ), 0 < ρ → f.coeff d ≠ 0 → ((∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff d‖ * ρ ^ d) → d ≤ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ((∀ j, d < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff d‖ * ρ ^ d) → Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) ≤ d) := by sorry
