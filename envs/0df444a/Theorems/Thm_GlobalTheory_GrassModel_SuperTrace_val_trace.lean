-- Prove2me | Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_val_trace
-- name    : GlobalTheory.GrassModel.SuperTrace.val_trace
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:45.468519+00:00
-- url     : https://prove2.me/theorems/a73dfbe2-76bc-44c9-861b-d3656b3bb241
-- title:
--   Super Trace: val trace
-- statement:
--   The Super Trace construction uses the val trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L85-L87

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

theorem GlobalTheory.GrassModel.SuperTrace.val_trace {r : Type*} [Fintype r] (M : Matrix r r (EvenPart n)) :
    ((EvenPart n).val M.trace) = (M.map (EvenPart n).val).trace := by sorry
