-- Prove2me | Theorems.Thm_GlobalTheory_card_roots_closedBall_eq_dominantIndex
-- name    : GlobalTheory.card_roots_closedBall_eq_dominantIndex
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:42.897988+00:00
-- url     : https://prove2.me/theorems/d0f64f71-df45-42bf-a0e3-c1a17cb71333
-- title:
--   Global Theory: card roots closed Ball eq dominant Index
-- statement:
--   The Global Theory construction uses the card roots closed Ball eq dominant Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardRootsClosedBallEqDominantIndex.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardRootsClosedBallEqDominantIndex.lean#L42-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NewtonPolygonLastDominantIndexMulXSubCStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NewtonPolygonDominantIndexXSubCMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallEqDominantIndex
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

theorem GlobalTheory.card_roots_closedBall_eq_dominantIndex :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by sorry
