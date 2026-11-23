-- Prove2me | Theorems.Thm_GlobalTheory_TruncGauss_qf_smul
-- name    : GlobalTheory.TruncGauss.qf_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:08.369564+00:00
-- url     : https://prove2.me/theorems/e51cd1e0-d01f-4efc-870c-65e388ee31c2
-- title:
--   Trunc Gauss: qf smul
-- statement:
--   The Trunc Gauss construction uses the qf smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L16-L18

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

theorem GlobalTheory.TruncGauss.qf_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    qf (c • A) w = c * qf A w := by sorry
