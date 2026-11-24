-- Prove2me | Theorems.Thm_GlobalTheory_T_fourier_harmonicMonomial_mul_gaussian_complex
-- name    : GlobalTheory.T.fourier_harmonicMonomial_mul_gaussian_complex
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:40:52.722506+00:00
-- url     : https://prove2.me/theorems/440de209-2459-4310-ad84-48385591386d
-- title:
--   T: fourier harmonic Monomial mul gaussian complex
-- statement:
--   The T construction uses the fourier harmonic Monomial mul gaussian complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierHarmonicMonomialMulGaussianComplexStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierHarmonicMonomialMulGaussianComplexStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierHarmonicMonomialMulGaussianComplex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierHarmonicMonomialMulGaussianComplexStatement
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

theorem GlobalTheory.T.fourier_harmonicMonomial_mul_gaussian_complex : ∀ (k : ℤ) (l : ℂ), 𝓕 (fun w : ℂ => GlobalTheory.HeckeTheta.hmon k w * Complex.exp ((-2 * Real.pi * ‖w‖ ^ 2 : ℝ) : ℂ)) l = (1 / 2 : ℂ) * (-Complex.I) ^ k.natAbs * (GlobalTheory.HeckeTheta.hmon k (l / 2) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by sorry
