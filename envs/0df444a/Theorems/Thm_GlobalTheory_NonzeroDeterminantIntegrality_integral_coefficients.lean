-- Prove2me | Theorems.Thm_GlobalTheory_NonzeroDeterminantIntegrality_integral_coefficients
-- name    : GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:40.912389+00:00
-- url     : https://prove2.me/theorems/efd72ff7-6957-51bc-b631-f52d08aec51d
-- title:
--   Nonzero Determinant Integrality: integral coefficients
-- statement:
--   The Nonzero Determinant Integrality construction uses the integral coefficients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralCoefficients.lean#L38-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralCoefficients.lean#L38-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonzeroDeterminantIntegrality
open Matrix

theorem GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients : ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁]
    (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a : W, i₁ a ≠ 0 → IsUnit a) →
    ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W),
    (∀ c : Λ → K₁, (∀ i : I, ∑ l : Λ, c l * i₁ (u i l) = 0) → c = 0) →
    ∀ (w : I → W) (z : Λ → K₀), (∀ i : I, i₀ (w i) = ∑ l : Λ, z l * i₀ (u i l)) →
    ∃ z₀ : Λ → W, (∀ l : Λ, i₀ (z₀ l) = z l) ∧ ∀ i : I, w i = ∑ l : Λ, z₀ l * u i l := by sorry
