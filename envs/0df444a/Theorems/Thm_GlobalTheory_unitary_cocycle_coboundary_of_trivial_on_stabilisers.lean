-- Prove2me | Theorems.Thm_GlobalTheory_unitary_cocycle_coboundary_of_trivial_on_stabilisers
-- name    : GlobalTheory.unitary_cocycle_coboundary_of_trivial_on_stabilisers
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:10.608958+00:00
-- url     : https://prove2.me/theorems/308d75a0-60e2-5d18-b261-5dad308ed608
-- title:
--   Global Theory: unitary cocycle coboundary of trivial on stabilisers
-- statement:
--   The Global Theory construction uses the unitary cocycle coboundary of trivial on stabilisers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryCocycleCoboundaryOfTrivialOnStabilisers.lean#L5-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryCocycleCoboundaryOfTrivialOnStabilisers.lean#L5-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCocycleCoboundaryOfTrivialOnStabilisers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.unitary_cocycle_coboundary_of_trivial_on_stabilisers :
    ∀ {X G : Type} [Group G] (mv : X → G → X) (z : X → G → ℂ), (∀ x, mv x 1 = x) →
      (∀ x g g', mv x (g * g') = mv (mv x g) g') → (∀ x g, ‖z x g‖ = 1) →
      (∀ x g g', z x (g * g') = z x g * z (mv x g) g') → (∀ x g, mv x g = x → z x g = 1) →
      ∃ c : X → ℂ, (∀ x, ‖c x‖ = 1) ∧ ∀ x g, c x * z x g = c (mv x g) := by sorry
