-- Prove2me | Theorems.Thm_GlobalTheory_unitary_isCayley_of_det_ne_zero
-- name    : GlobalTheory.unitary_isCayley_of_det_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:29.981022+00:00
-- url     : https://prove2.me/theorems/28b3a7f1-46df-49c4-aa5e-cd17eee324cc
-- title:
--   Global Theory: unitary is Cayley of det ne zero
-- statement:
--   The Global Theory construction uses the unitary is Cayley of det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryFamilyEqCayleyOfSkewFamily.lean#L51-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryFamilyEqCayleyOfSkewFamily.lean#L51-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory
variable {n : ℕ}

theorem GlobalTheory.unitary_isCayley_of_det_ne_zero : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
    (∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1) → (∀ σ, (1 + X σ).det ≠ 0) →
    ∃ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) ∧
      (∀ σ, (1 - Y σ).det ≠ 0) ∧ ∀ σ, (1 + Y σ) * (1 - Y σ)⁻¹ = X σ := by sorry
