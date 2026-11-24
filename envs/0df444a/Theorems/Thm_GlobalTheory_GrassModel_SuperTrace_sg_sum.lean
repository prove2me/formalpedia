-- Prove2me | Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_sg_sum
-- name    : GlobalTheory.GrassModel.SuperTrace.sg_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:52.622955+00:00
-- url     : https://prove2.me/theorems/43574d40-c9ea-49f4-81aa-2cb110a3ef7b
-- title:
--   Super Trace: sg sum
-- statement:
--   The Super Trace construction uses the sg sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TracePowGrassmannBlockCurvatureSupertraceZero.lean#L19-L25

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

theorem GlobalTheory.GrassModel.SuperTrace.sg_sum {ι : Type*} (s : Finset ι) (m : ℕ) (f : ι → Big n) (h : ∀ i ∈ s, Sg m (f i)) :
    Sg m (∑ i ∈ s, f i) := by sorry
