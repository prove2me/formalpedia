-- Prove2me | Theorems.Thm_GlobalTheory_IsLogBoundedScalar_mono
-- name    : GlobalTheory.IsLogBoundedScalar.mono
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:21.325161+00:00
-- url     : https://prove2.me/theorems/0384b064-8434-43e3-970c-affb3735ed15
-- title:
--   Is Log Bounded Scalar: mono
-- statement:
--   The Is Log Bounded Scalar construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L297-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L297-L299

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

theorem GlobalTheory.IsLogBoundedScalar.mono (hg : IsLogBoundedScalar S w U g) {V : Set X} (hV : V ⊆ U) :
    IsLogBoundedScalar S w V g := by sorry
