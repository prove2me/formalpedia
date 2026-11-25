-- Prove2me | Theorems.Thm_GlobalTheory_notMem_coordDivisor
-- name    : GlobalTheory.notMem_coordDivisor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:54.304679+00:00
-- url     : https://prove2.me/theorems/853952c8-6b06-4022-b3b8-577e1f910231
-- title:
--   Global Theory: not Mem coord Divisor
-- statement:
--   The Global Theory construction uses the not Mem coord Divisor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L20-L22

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

theorem GlobalTheory.notMem_coordDivisor {S : Finset κ} {w : X → κ → ℂ} {x : X} :
    x ∉ coordDivisor S w ↔ ∀ j ∈ S, w x j ≠ 0 := by sorry
