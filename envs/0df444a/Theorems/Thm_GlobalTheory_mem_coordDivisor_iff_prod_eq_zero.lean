-- Prove2me | Theorems.Thm_GlobalTheory_mem_coordDivisor_iff_prod_eq_zero
-- name    : GlobalTheory.mem_coordDivisor_iff_prod_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:59.987468+00:00
-- url     : https://prove2.me/theorems/a24ab313-29f6-4d7b-8066-02ec1d460a69
-- title:
--   Global Theory: mem coord Divisor iff prod eq zero
-- statement:
--   The Global Theory construction uses the mem coord Divisor iff prod eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L24-L26

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

theorem GlobalTheory.mem_coordDivisor_iff_prod_eq_zero {S : Finset κ} {w : X → κ → ℂ} {x : X} :
    x ∈ coordDivisor S w ↔ ∏ j ∈ S, w x j = 0 := by sorry
