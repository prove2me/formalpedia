-- Prove2me | Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_val_pow
-- name    : GlobalTheory.GrassModel.SuperTrace.val_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:34.718704+00:00
-- url     : https://prove2.me/theorems/f46da87b-8512-4e97-8438-814588802af4
-- title:
--   Super Trace: val pow
-- statement:
--   The Super Trace construction uses the val pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L89-L91

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

theorem GlobalTheory.GrassModel.SuperTrace.val_pow {r : Type*} [Fintype r] [DecidableEq r] (M : Matrix r r (EvenPart n)) (k : ℕ) :
    (M ^ k).map (EvenPart n).val = (M.map (EvenPart n).val) ^ k := by sorry
