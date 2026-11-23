-- Prove2me | Theorems.Thm_GlobalTheory_TruncGauss_qf_one
-- name    : GlobalTheory.TruncGauss.qf_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:19.662157+00:00
-- url     : https://prove2.me/theorems/9ce3cec6-a7e9-407c-8e2e-a4a64090da01
-- title:
--   Trunc Gauss: qf one
-- statement:
--   The Trunc Gauss construction uses the qf one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L20-L25

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

theorem GlobalTheory.TruncGauss.qf_one {n : ℕ} (w : V n) : qf (1 : Matrix (Fin n) (Fin n) ℂ) w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by sorry
