-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_det_mul_right
-- name    : GlobalTheory.SW.LinChange.det_mul_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:34.325031+00:00
-- url     : https://prove2.me/theorems/78c925cb-682a-4e54-b8cf-1ea7f1f67b38
-- title:
--   Lin Change: det mul right
-- statement:
--   The Lin Change construction uses the det mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L244-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L244-L254

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.LinChange.det_mul_right [DecidableEq ι] (A : Matrix ι ι K) :
    LinearMap.det (mulRightLinearMap κ K A) = A.det ^ Fintype.card κ := by sorry
