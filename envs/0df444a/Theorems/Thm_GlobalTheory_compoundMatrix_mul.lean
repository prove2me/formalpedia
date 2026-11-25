-- Prove2me | Theorems.Thm_GlobalTheory_compoundMatrix_mul
-- name    : GlobalTheory.compoundMatrix_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:57.823717+00:00
-- url     : https://prove2.me/theorems/530032dc-c477-4164-a739-9ee5416a9674
-- title:
--   Global Theory: compound Matrix mul
-- statement:
--   The Global Theory construction uses the compound Matrix mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L548-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L548-L551

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {l n o : Type*} [LinearOrder l] [LinearOrder n] [LinearOrder o]

theorem GlobalTheory.compoundMatrix_mul [Fintype n] (k : ℕ) (A : Matrix l n ℂ) (A' : Matrix n o ℂ) :
    compoundMatrix k (A * A') = compoundMatrix k A * compoundMatrix k A' := by sorry
