-- Prove2me | Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_msg_mul
-- name    : GlobalTheory.GrassModel.SuperTrace.msg_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:06.655385+00:00
-- url     : https://prove2.me/theorems/3e909835-e800-4ec8-94cb-8e67a6e6b95a
-- title:
--   Super Trace: msg mul
-- statement:
--   The Super Trace construction uses the msg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L44-L46

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

theorem GlobalTheory.GrassModel.SuperTrace.msg_mul {r s t : Type*} [Fintype s] {m l : ℕ} {M : Matrix r s (Big n)}
    {N : Matrix s t (Big n)} (hM : MSg m M) (hN : MSg l N) : MSg (m + l) (M * N) := by sorry
