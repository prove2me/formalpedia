-- Prove2me | Theorems.Thm_GlobalTheory_antidiag_twisted_norm
-- name    : GlobalTheory.antidiag_twisted_norm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:50.902887+00:00
-- url     : https://prove2.me/theorems/0f566abf-c60c-4fca-8806-ceeeba8ae462
-- title:
--   Global Theory: antidiag twisted norm
-- statement:
--   The Global Theory construction uses the antidiag twisted norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntidiagTwistedNorm.lean#L7-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntidiagTwistedNorm.lean#L7-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AntidiagTwistedNorm
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

theorem GlobalTheory.antidiag_twisted_norm : ∀ (E : Type) [Field E] (c : E ≃+* E), (∀ x, c (c x) = x) → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) E), Φ = Matrix.of (fun i j : Fin a => if j = i.rev then (-1 : E) ^ (i : ℕ) else 0) → Φ.transpose = (-1 : E) ^ (a - 1) • Φ ∧ IsUnit Φ.det ∧ ∀ δ : Matrix (Fin a) (Fin a) E, IsUnit δ.det → δ * (Φ * ((δ.map c).transpose)⁻¹ * Φ⁻¹) = (-1 : E) ^ (a - 1) • ((δ * Φ) * (((δ * Φ).map c).transpose)⁻¹) ∧ Φ * (((Φ * ((δ.map c).transpose)⁻¹ * Φ⁻¹).map c).transpose)⁻¹ * Φ⁻¹ = δ := by sorry
