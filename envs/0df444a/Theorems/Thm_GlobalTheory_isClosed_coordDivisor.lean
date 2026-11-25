-- Prove2me | Theorems.Thm_GlobalTheory_isClosed_coordDivisor
-- name    : GlobalTheory.isClosed_coordDivisor
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:20.895718+00:00
-- url     : https://prove2.me/theorems/04a3d826-7f8b-4682-9339-6c292cf1f616
-- title:
--   Global Theory: is Closed coord Divisor
-- statement:
--   The Global Theory construction uses the is Closed coord Divisor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L28-L33

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
variable {κ X : Type*}

theorem GlobalTheory.isClosed_coordDivisor [TopologicalSpace X] (S : Finset κ) {w : X → κ → ℂ}
    (hw : ∀ j ∈ S, Continuous fun x => w x j) : IsClosed (coordDivisor S w) := by sorry
