-- Prove2me | Theorems.Thm_GlobalTheory_NarrowGauss_gauss_apply
-- name    : GlobalTheory.NarrowGauss.gauss_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:58:04.764647+00:00
-- url     : https://prove2.me/theorems/66ff16bf-7ded-493e-a6e2-745a20598a8a
-- title:
--   Narrow Gauss: gauss apply
-- statement:
--   The Narrow Gauss construction uses the gauss apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NarrowGaussConvolutionDense.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NarrowGaussConvolutionDense.lean#L17-L30

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartzStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NarrowGaussConvolutionDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NarrowGauss
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.NarrowGauss.gauss_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gauss c hc x = Complex.exp (-(c : ℂ) * ‖x‖ ^ 2) := by sorry
