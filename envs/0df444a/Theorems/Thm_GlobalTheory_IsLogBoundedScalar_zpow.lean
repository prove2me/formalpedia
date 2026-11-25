-- Prove2me | Theorems.Thm_GlobalTheory_IsLogBoundedScalar_zpow
-- name    : GlobalTheory.IsLogBoundedScalar.zpow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:16.425425+00:00
-- url     : https://prove2.me/theorems/2a8d6467-c2ec-40b7-b6af-a9721da7982c
-- title:
--   Is Log Bounded Scalar: zpow
-- statement:
--   The Is Log Bounded Scalar construction uses the zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L347-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L347-L349

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

theorem GlobalTheory.IsLogBoundedScalar.zpow (hg : IsLogBoundedScalar S w U g) (k : ℤ) :
    IsLogBoundedScalar S w U fun x => g x ^ k := by sorry
