-- Prove2me | Theorems.Thm_GlobalTheory_compoundMatrix_inv
-- name    : GlobalTheory.compoundMatrix_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:04.712789+00:00
-- url     : https://prove2.me/theorems/c98b5784-645c-4c55-9058-811835b9343f
-- title:
--   Global Theory: compound Matrix inv
-- statement:
--   The Global Theory construction uses the compound Matrix inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L572-L576
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L572-L576

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
variable [Fintype n]

theorem GlobalTheory.compoundMatrix_inv (k : ℕ) {A : Matrix n n ℂ} (hA : IsUnit A) :
    (compoundMatrix k A)⁻¹ = compoundMatrix k A⁻¹ := by sorry
