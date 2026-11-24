-- Prove2me | Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_pow_mul_left
-- name    : GlobalTheory.GrassModel.SuperTrace.pow_mul_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:57:34.424538+00:00
-- url     : https://prove2.me/theorems/55fc8512-47c7-45c0-a596-2cb7bc556bb4
-- title:
--   Super Trace: pow mul left
-- statement:
--   The Super Trace construction uses the pow mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L59-L64

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

theorem GlobalTheory.GrassModel.SuperTrace.pow_mul_left {p q : ℕ} {R : Type*} [Semiring R] (A : Matrix (Fin p) (Fin q) R)
    (B : Matrix (Fin q) (Fin p) R) (m : ℕ) : (A * B) ^ m * A = A * (B * A) ^ m := by sorry
