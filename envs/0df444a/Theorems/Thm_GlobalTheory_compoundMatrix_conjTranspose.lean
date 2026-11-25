-- Prove2me | Theorems.Thm_GlobalTheory_compoundMatrix_conjTranspose
-- name    : GlobalTheory.compoundMatrix_conjTranspose
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:10.663558+00:00
-- url     : https://prove2.me/theorems/00a0f3a7-2b3d-4975-afe0-9c60133b1aec
-- title:
--   Global Theory: compound Matrix conj Transpose
-- statement:
--   The Global Theory construction uses the compound Matrix conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L553-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L553-L557

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

theorem GlobalTheory.compoundMatrix_conjTranspose (k : ℕ) (A : Matrix l n ℂ) :
    compoundMatrix k Aᴴ = (compoundMatrix k A)ᴴ := by sorry
