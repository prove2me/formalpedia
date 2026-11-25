-- Prove2me | Theorems.Thm_GlobalTheory_IsLogBoundedScalar_of_pow
-- name    : GlobalTheory.IsLogBoundedScalar.of_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:32.525887+00:00
-- url     : https://prove2.me/theorems/c4038c46-7cbf-4c47-ac3e-d3f99cfde1ba
-- title:
--   Is Log Bounded Scalar: of pow
-- statement:
--   The Is Log Bounded Scalar construction uses the of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L355-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L355-L357

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
variable {κ κ' X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X} {g g' : X → ℝ}
open GlobalTheory.IsLogBoundedScalar

theorem GlobalTheory.IsLogBoundedScalar.of_pow {k : ℕ} (hk : k ≠ 0) (h0 : ∀ x ∈ U, x ∉ coordDivisor S w → 0 ≤ g x)
    (hg : IsLogBoundedScalar S w U fun x => g x ^ k) : IsLogBoundedScalar S w U g := by sorry
