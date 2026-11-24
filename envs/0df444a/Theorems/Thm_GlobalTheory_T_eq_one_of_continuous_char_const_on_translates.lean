-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_one_of_continuous_char_const_on_translates
-- name    : GlobalTheory.T.eq_one_of_continuous_char_const_on_translates
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:33:08.436876+00:00
-- url     : https://prove2.me/theorems/271ab64a-cce7-48b6-9338-98e00dfdcaf5
-- title:
--   T: eq one of continuous char const on translates
-- statement:
--   The T construction uses the eq one of continuous char const on translates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CharConstOnTranslatesTrivialStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CharConstOnTranslatesTrivialStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivialStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_one_of_continuous_char_const_on_translates : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ψ : (ι → ℂˣ) →* ℂˣ) (θ : ι → ℂ) (T : Set (ι → ℝ)) (C : ℝ) (c : ℂˣ), Continuous ψ → (∀ i, (θ i).im ≠ 0) → (∀ y : ι → ℝ, ∃ a ∈ T, ‖a - y‖ ≤ C) → (∀ a ∈ T, ∀ z : ι → ℂˣ, (∀ i, (z i : ℂ) = a i + θ i) → ψ z = c) → ψ = 1 := by sorry
