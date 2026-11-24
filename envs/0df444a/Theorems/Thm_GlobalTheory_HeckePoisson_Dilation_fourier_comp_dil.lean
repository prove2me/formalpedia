-- Prove2me | Theorems.Thm_GlobalTheory_HeckePoisson_Dilation_fourier_comp_dil
-- name    : GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:04:26.217943+00:00
-- url     : https://prove2.me/theorems/b0389ee8-2b24-4a5f-a0bc-ddce91b5bfbc
-- title:
--   Dilation: fourier comp dil
-- statement:
--   The Dilation construction uses the fourier comp dil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierCompCoordDilationByHalfExp.lean#L65-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierCompCoordDilationByHalfExp.lean#L65-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierCompCoordDilationByHalfExp
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
open GlobalTheory GlobalTheory.HeckePoisson GlobalTheory.HeckePoisson.Dilation
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
variable {I : Type} [Fintype I]

theorem GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ)
    (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l =
      (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by sorry
