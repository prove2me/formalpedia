-- Prove2me | Theorems.Thm_GlobalTheory_TruncGauss_qf_shift_re
-- name    : GlobalTheory.TruncGauss.qf_shift_re
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:49.473878+00:00
-- url     : https://prove2.me/theorems/1e5368c9-ec24-4de1-80fe-c35d60ad60df
-- title:
--   Trunc Gauss: qf shift re
-- statement:
--   The Trunc Gauss construction uses the qf shift re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L76-L80

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

theorem GlobalTheory.TruncGauss.qf_shift_re {n : ℕ} (m η : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    (qf ((m : ℂ) • (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) w).re =
      m * ((qf H w).re + η * ‖w‖ ^ 2) := by sorry
