-- Prove2me | Theorems.Thm_GlobalTheory_TruncGauss_exists_det_shift
-- name    : GlobalTheory.TruncGauss.exists_det_shift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:10.610129+00:00
-- url     : https://prove2.me/theorems/a8f0cf4f-5831-4f8c-a3a9-e72d695852a8
-- title:
--   Trunc Gauss: exists det shift
-- statement:
--   The Trunc Gauss construction uses the exists det shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L56-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L56-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.TruncGauss

theorem GlobalTheory.TruncGauss.exists_det_shift (n : ℕ) (C r : ℝ) (hr : 0 < r) : ∃ η : ℝ, 0 < η ∧
    ∀ H : Matrix (Fin n) (Fin n) ℂ, (∀ j l, ‖H j l‖ ≤ C) →
      ‖(H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ < r := by sorry
