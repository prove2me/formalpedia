-- Prove2me | Theorems.Thm_GlobalTheory_TruncGauss_qf_smul_one_re
-- name    : GlobalTheory.TruncGauss.qf_smul_one_re
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:41.973607+00:00
-- url     : https://prove2.me/theorems/cf4ec8e3-84f5-43f6-ab2c-6958ee8bb04f
-- title:
--   Trunc Gauss: qf smul one re
-- statement:
--   The Trunc Gauss construction uses the qf smul one re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L72-L74

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

theorem GlobalTheory.TruncGauss.qf_smul_one_re {n : ℕ} (c : ℝ) (w : V n) :
    (qf ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) w).re = c * ‖w‖ ^ 2 := by sorry
