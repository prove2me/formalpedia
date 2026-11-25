-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_closure_gaussian_convolutions
-- name    : GlobalTheory.T.mem_closure_gaussian_convolutions
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:24.041344+00:00
-- url     : https://prove2.me/theorems/44c92dda-ac1b-5efa-a7ff-d230b2ec1ce3
-- title:
--   T: mem closure gaussian convolutions
-- statement:
--   The T construction uses the mem closure gaussian convolutions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NarrowGaussConvolutionDenseStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NarrowGaussConvolutionDenseStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NarrowGaussConvolutionDense
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NarrowGaussConvolutionDenseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_closure_gaussian_convolutions : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ),
    f ∈ closure {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} := by sorry
