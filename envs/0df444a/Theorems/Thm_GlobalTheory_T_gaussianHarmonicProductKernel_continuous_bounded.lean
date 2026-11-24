-- Prove2me | Theorems.Thm_GlobalTheory_T_gaussianHarmonicProductKernel_continuous_bounded
-- name    : GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:47.376243+00:00
-- url     : https://prove2.me/theorems/eaf46c4d-bcef-4f6e-97eb-06f5ca882eac
-- title:
--   T: gaussian Harmonic Product Kernel continuous bounded
-- statement:
--   The T construction uses the gaussian Harmonic Product Kernel continuous bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianHarmonicProductKernelContinuousBoundedStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianHarmonicProductKernelContinuousBoundedStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianHarmonicProductKernelContinuousBounded
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianHarmonicProductKernelContinuousBoundedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded : ∀ (I : Type) [Fintype I] (n : I → ℤ), Continuous (fun w : EuclideanSpace ℂ I => GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)) ∧ ∃ C : ℝ, ∀ w : EuclideanSpace ℂ I, ‖GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)‖ ≤ C * Real.exp (-Real.pi * ‖w‖ ^ 2) := by sorry
