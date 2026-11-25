-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeSlice_gaussian_slice_invariant
-- name    : GlobalTheory.HCXi.ConeSlice.gaussian_slice_invariant
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:22.844355+00:00
-- url     : https://prove2.me/theorems/5c4af2f7-887d-451c-979e-692e8757c44f
-- title:
--   Cone Slice: gaussian slice invariant
-- statement:
--   The Cone Slice construction uses the gaussian slice invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L200-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L200-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibrationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeSlice

theorem GlobalTheory.HCXi.ConeSlice.gaussian_slice_invariant : ∀ (k : ℕ) (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), gᴴ * Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1) * g = Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1) → ∀ τ : ℝ, 0 ≤ τ → (∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))))))) = ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (Real.exp (-sqLen (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2)) : Fin (k + 1) → ℂ))) := by sorry
