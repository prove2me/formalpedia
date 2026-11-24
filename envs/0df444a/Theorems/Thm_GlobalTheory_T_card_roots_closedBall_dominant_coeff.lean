-- Prove2me | Theorems.Thm_GlobalTheory_T_card_roots_closedBall_dominant_coeff
-- name    : GlobalTheory.T.card_roots_closedBall_dominant_coeff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:28:37.941845+00:00
-- url     : https://prove2.me/theorems/2284d3f0-3c50-4ac0-90a3-6c50e8b71870
-- title:
--   T: card roots closed Ball dominant coeff
-- statement:
--   The T construction uses the card roots closed Ball dominant coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardRootsClosedBallEqDominantIndexStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardRootsClosedBallEqDominantIndexStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallEqDominantIndex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallEqDominantIndexStatement
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

theorem GlobalTheory.T.card_roots_closedBall_dominant_coeff : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by sorry
