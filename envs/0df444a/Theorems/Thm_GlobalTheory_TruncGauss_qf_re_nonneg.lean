-- Prove2me | Theorems.Thm_GlobalTheory_TruncGauss_qf_re_nonneg
-- name    : GlobalTheory.TruncGauss.qf_re_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:04.88185+00:00
-- url     : https://prove2.me/theorems/dc940e7b-e92b-4a6c-babd-06d927fec333
-- title:
--   Trunc Gauss: qf re nonneg
-- statement:
--   The Trunc Gauss construction uses the qf re nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L27-L35

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

theorem GlobalTheory.TruncGauss.qf_re_nonneg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (w : V n) :
    0 ≤ (qf H w).re := by sorry
