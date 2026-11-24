-- Prove2me | Theorems.Thm_GlobalTheory_SW_ip_self_nonneg_and_bounds
-- name    : GlobalTheory.SW.ip_self_nonneg_and_bounds
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:18:03.741695+00:00
-- url     : https://prove2.me/theorems/3210debd-0239-490f-9333-1cec0d272a31
-- title:
--   SW: ip self nonneg and bounds
-- statement:
--   The SW construction uses the ip self nonneg and bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInnerProductSelfNonnegBounds.lean#L153-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInnerProductSelfNonnegBounds.lean#L153-L220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open Matrix Complex
open scoped ComplexConjugate Real

theorem GlobalTheory.SW.ip_self_nonneg_and_bounds : ∀ (K κ ι : Type) [Field K] [NumberField K]
    [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → _root_.GlobalTheory.SW.HasLevel R φ →
    (_root_.GlobalTheory.SW.ip φ φ).im = 0 ∧ 0 ≤ (_root_.GlobalTheory.SW.ip φ φ).re ∧
    (∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) *
      (_root_.GlobalTheory.SW.ip φ φ).re) ∧
    (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → (_root_.GlobalTheory.SW.ip φ φ).re ≤
      (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * B ^ 2) ∧
    (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧ ∀ ψ, _root_.GlobalTheory.SW.IsSB ψ →
      ‖_root_.GlobalTheory.SW.ip φ ψ‖ ^ 2 ≤
        (_root_.GlobalTheory.SW.ip φ φ).re * (_root_.GlobalTheory.SW.ip ψ ψ).re := by sorry
