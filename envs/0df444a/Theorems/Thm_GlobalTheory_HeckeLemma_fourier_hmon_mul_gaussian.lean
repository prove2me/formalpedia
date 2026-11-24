-- Prove2me | Theorems.Thm_GlobalTheory_HeckeLemma_fourier_hmon_mul_gaussian
-- name    : GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:03:38.631802+00:00
-- url     : https://prove2.me/theorems/90b6582c-8432-4cd0-b35c-3f70c01aaaa1
-- title:
--   Hecke Lemma: fourier hmon mul gaussian
-- statement:
--   The Hecke Lemma construction uses the fourier hmon mul gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierHarmonicMonomialMulGaussianComplex.lean#L233-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierHarmonicMonomialMulGaussianComplex.lean#L233-L246

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierHarmonicMonomialMulGaussianComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
open GlobalTheory GlobalTheory.HeckeLemma
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

theorem GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian : ∀ (k : ℤ) (l : ℂ),
    𝓕 (fun w : ℂ => _root_.GlobalTheory.HeckeTheta.hmon k w *
        Complex.exp ((-2 * Real.pi * ‖w‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * (-Complex.I) ^ k.natAbs * (_root_.GlobalTheory.HeckeTheta.hmon k (l / 2) *
        Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by sorry
