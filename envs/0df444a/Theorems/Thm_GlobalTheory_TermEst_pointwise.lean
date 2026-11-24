-- Prove2me | Theorems.Thm_GlobalTheory_TermEst_pointwise
-- name    : GlobalTheory.TermEst.pointwise
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:03:31.651806+00:00
-- url     : https://prove2.me/theorems/a8c44360-0a91-49a5-9fec-147d4799888c
-- title:
--   Term Est: pointwise
-- statement:
--   The Term Est construction uses the pointwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianConvolutionSeriesCoefficientDescFactoria.lean#L7-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianConvolutionSeriesCoefficientDescFactoria.lean#L7-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianConvolutionSeriesCoefficientDescFactoria
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TermEst

theorem GlobalTheory.TermEst.pointwise (b c θ α s t H : ℝ) (hc : 0 < c) (hθ : 1 ≤ θ) (hα : 0 < α)
    (hk : c * θ ^ 2 ≤ α * (b + c)) (hs : 0 ≤ s) (ht : 0 ≤ t) (hH : 0 ≤ H) (i m : ℕ) :
    (2 * c) ^ (i + m) / (m.factorial : ℝ) * t ^ m * (Real.exp (-((b + c) * s ^ 2)) * H * s ^ (i + m)) ≤
      θ⁻¹ ^ m * Real.exp (c * α * t ^ 2) * ((2 * c * s) ^ i * H) := by sorry
