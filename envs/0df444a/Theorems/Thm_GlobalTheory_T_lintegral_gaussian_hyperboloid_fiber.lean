-- Prove2me | Theorems.Thm_GlobalTheory_T_lintegral_gaussian_hyperboloid_fiber
-- name    : GlobalTheory.T.lintegral_gaussian_hyperboloid_fiber
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:02:34.516458+00:00
-- url     : https://prove2.me/theorems/76a89de7-bfad-4600-80eb-ba96bf535c25
-- title:
--   T: lintegral gaussian hyperboloid fiber
-- statement:
--   The T construction uses the lintegral gaussian hyperboloid fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiberStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiberStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiber
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lintegral_gaussian_hyperboloid_fiber : ∀ (k : ℕ) (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), gᴴ * Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1) * g = Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1) → ∀ τ : ℝ, 0 ≤ τ → (∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))))))) = ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (Real.exp (-sqLen (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2)) : Fin (k + 1) → ℂ))) := by sorry
