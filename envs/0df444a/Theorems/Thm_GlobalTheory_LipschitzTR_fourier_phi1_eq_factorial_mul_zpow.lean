-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_fourier_phi1_eq_factorial_mul_zpow
-- name    : GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:49.207867+00:00
-- url     : https://prove2.me/theorems/e8dbc3ea-e264-4709-8cbf-ec10d181c4c7
-- title:
--   Lipschitz TR: fourier phi1 eq factorial mul zpow
-- statement:
--   The Lipschitz TR construction uses the fourier phi1 eq factorial mul zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierLipschitzOneVariableKernelEq.lean#L84-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierLipschitzOneVariableKernelEq.lean#L84-L135

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR
open Set Filter Topology

theorem GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow : ∀ (k : ℕ), 2 ≤ k → Even k → ∀ (w : ℂ), w.im ≠ 0 → ∀ (x : ℝ),
    𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) := by sorry
