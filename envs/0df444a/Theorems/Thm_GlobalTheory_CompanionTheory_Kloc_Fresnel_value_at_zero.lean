-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_value_at_zero
-- name    : GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:03.993086+00:00
-- url     : https://prove2.me/theorems/a0457cf1-3a4d-4be6-9e0c-607cd241cea1
-- title:
--   Fresnel: value at zero
-- statement:
--   The Fresnel construction uses the value at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L418-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L418-L443

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {m n : ℕ}

theorem GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero : ∀ (m n : ℕ) (C s : ℂ) (k : ℝ), C ≠ 0 → k ≠ 0 → ‖s‖ = 2 * |k| → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, (fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ⇑φ))))) 0 = c * ∫ v : Fin m → Fin n → ℂ, φ v := by sorry
