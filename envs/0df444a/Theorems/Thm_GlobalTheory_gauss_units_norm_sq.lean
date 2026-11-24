-- Prove2me | Theorems.Thm_GlobalTheory_gauss_units_norm_sq
-- name    : GlobalTheory.gauss_units_norm_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:06.163922+00:00
-- url     : https://prove2.me/theorems/58581aa0-d18d-4a62-8553-999828aac039
-- title:
--   Global Theory: gauss units norm sq
-- statement:
--   The Global Theory construction uses the gauss units norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussUnitsNormSq.lean#L68-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussUnitsNormSq.lean#L68-L176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussUnitsNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ComplexConjugate Finset
open GlobalTheory
open GaussUnits

theorem GlobalTheory.gauss_units_norm_sq : ∀ {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [Fintype Rˣ]
    (m : Ideal R), (∀ x : R, IsUnit x ↔ x ∉ m) → ∀ (ψ : AddChar R ℂ),
    (∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) → ∀ (χ : Rˣ → ℂ), (∀ u v, χ (u * v) = χ u * χ v) →
    (∀ u, ‖χ u‖ = 1) → ∀ (t₀ : Rˣ), (∀ x ∈ m, ((t₀ : R) - 1) * x = 0) → χ t₀ ≠ 1 →
    ‖∑ u : Rˣ, (χ u)⁻¹ * ψ u‖ ^ 2 = Fintype.card R := by sorry
