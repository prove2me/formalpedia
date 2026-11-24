-- Prove2me | Theorems.Thm_GlobalTheory_T_fourier_comp_coordDilationByHalfExp
-- name    : GlobalTheory.T.fourier_comp_coordDilationByHalfExp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:40:34.19641+00:00
-- url     : https://prove2.me/theorems/0c8b57e5-bd53-48bf-831a-183eaefeac07
-- title:
--   T: fourier comp coord Dilation By Half Exp
-- statement:
--   The T construction uses the fourier comp coord Dilation By Half Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierCompCoordDilationByHalfExpStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierCompCoordDilationByHalfExpStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierCompCoordDilationByHalfExp
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierCompCoordDilationByHalfExpStatement
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

theorem GlobalTheory.T.fourier_comp_coordDilationByHalfExp : ∀ (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ) (l : EuclideanSpace ℂ I), 𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l = (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by sorry
