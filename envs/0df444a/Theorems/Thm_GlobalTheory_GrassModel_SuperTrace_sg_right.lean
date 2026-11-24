-- Prove2me | Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_sg_right
-- name    : GlobalTheory.GrassModel.SuperTrace.sg_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:42.669799+00:00
-- url     : https://prove2.me/theorems/5c6ac1a1-f2d4-4ade-a7c2-9b78798987f9
-- title:
--   Super Trace: sg right
-- statement:
--   The Super Trace construction uses the sg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L38-L40

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

theorem GlobalTheory.GrassModel.SuperTrace.sg_right (b : Fin n) : Sg 1 ((1 : Ext n) ⊗ₜ vec n b) := by sorry
