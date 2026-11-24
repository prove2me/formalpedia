-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_det_mul_left
-- name    : GlobalTheory.SW.LinChange.det_mul_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:25.692856+00:00
-- url     : https://prove2.me/theorems/4084c947-eecc-41a1-ac4e-3fdc41ce1782
-- title:
--   Lin Change: det mul left
-- statement:
--   The Lin Change construction uses the det mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L256-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L256-L262

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

theorem GlobalTheory.SW.LinChange.det_mul_left [DecidableEq κ] (A : Matrix κ κ K) :
    LinearMap.det (mulLeftLinearMap ι K A) = A.det ^ Fintype.card ι := by sorry
