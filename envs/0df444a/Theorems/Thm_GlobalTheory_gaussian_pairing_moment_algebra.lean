-- Prove2me | Theorems.Thm_GlobalTheory_gaussian_pairing_moment_algebra
-- name    : GlobalTheory.gaussian_pairing_moment_algebra
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:13.540181+00:00
-- url     : https://prove2.me/theorems/80ab9ce1-2988-4552-a0f3-55949fdf5373
-- title:
--   Global Theory: gaussian pairing moment algebra
-- statement:
--   The Global Theory construction uses the gaussian pairing moment algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GaussianPairingMomentAlgebra.lean#L7-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GaussianPairingMomentAlgebra.lean#L7-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GaussianPairingMomentAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory

theorem GlobalTheory.gaussian_pairing_moment_algebra : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ) (t f : ℂ) (p q : σ → ℂ) (m n : Matrix σ σ ℂ), Sᵀ = S → Tᵀ = T → IsUnit (1 - (t ^ 2) • (T * S)).det → p = t • (f • y + T *ᵥ q) → q = t • (f • x + S *ᵥ p) → m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec y q + t • (T * n) → n = t • vecMulVec x q + t • (S * m) → let w : σ → ℂ := (1 - (t ^ 2) • (T * S))⁻¹ *ᵥ (y + t • T *ᵥ x); let u : σ → ℂ := x + t • S *ᵥ w; f * (x ⬝ᵥ y) + x ⬝ᵥ T *ᵥ q + y ⬝ᵥ S *ᵥ p + (S * m * Tᵀ).trace = f * (u ⬝ᵥ w + t * (T * S * (1 - (t ^ 2) • (T * S))⁻¹).trace) := by sorry
