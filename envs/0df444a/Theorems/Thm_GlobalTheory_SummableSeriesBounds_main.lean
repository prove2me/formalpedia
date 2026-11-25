-- Prove2me | Theorems.Thm_GlobalTheory_SummableSeriesBounds_main
-- name    : GlobalTheory.SummableSeriesBounds.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:28.137385+00:00
-- url     : https://prove2.me/theorems/bde8e770-4dd4-5267-a504-2a8580c0657f
-- title:
--   Summable Series Bounds: main
-- statement:
--   The Summable Series Bounds construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L213-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L213-L225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem GlobalTheory.SummableSeriesBounds.main (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    (π : C) (hπ : ‖π‖ < 1) :
    ∃ (B : Subring (PowerSeries C)) (ev : B →+* C) (t : B),
      (∀ Φ : PowerSeries C, Φ ∈ B ↔ ∃ b : ℝ, ∀ n : ℕ, ‖coeff n Φ‖ ≤ b) ∧
      (∀ Φ : B, ev Φ = ∑' n : ℕ, coeff n (Φ : PowerSeries C) * π ^ n) ∧ t ≠ 0 ∧
      (∀ Φ : B, ev Φ = 0 ↔ t ∣ Φ) ∧ ∀ Φ : B, Φ ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ Φ := by sorry
