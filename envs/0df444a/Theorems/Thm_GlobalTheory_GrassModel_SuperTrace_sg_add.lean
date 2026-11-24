-- Prove2me | Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_sg_add
-- name    : GlobalTheory.GrassModel.SuperTrace.sg_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:47.878044+00:00
-- url     : https://prove2.me/theorems/2d8ab4cf-7997-4606-b0e2-7b7a2aec9cc1
-- title:
--   Super Trace: sg add
-- statement:
--   The Super Trace construction uses the sg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L16-L17

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TracePowGrassmannBlockCurvatureSupertraceZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open GlobalTheory GlobalTheory.GrassModel GlobalTheory.GrassModel.SuperTrace
variable {n : ℕ}

theorem GlobalTheory.GrassModel.SuperTrace.sg_add {m : ℕ} {z w : Big n} (hz : Sg m z) (hw : Sg m w) : Sg m (z + w) := by sorry
