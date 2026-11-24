-- Prove2me | Theorems.Thm_GlobalTheory_TruncGauss_qf_add
-- name    : GlobalTheory.TruncGauss.qf_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:36.380301+00:00
-- url     : https://prove2.me/theorems/4b010082-6426-4cf2-b33a-ff608158ede1
-- title:
--   Trunc Gauss: qf add
-- statement:
--   The Trunc Gauss construction uses the qf add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L12-L14

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

theorem GlobalTheory.TruncGauss.qf_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    qf (A + B) w = qf A w + qf B w := by sorry
