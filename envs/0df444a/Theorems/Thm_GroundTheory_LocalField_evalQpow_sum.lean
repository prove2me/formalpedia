-- Prove2me | Theorems.Thm_GroundTheory_LocalField_evalQpow_sum
-- name    : GroundTheory.LocalField.evalQpow_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:54.481698+00:00
-- url     : https://prove2.me/theorems/0f53e016-78e1-513d-816c-3e99dd2dd597
-- title:
--   Local Field: eval Qpow sum
-- statement:
--   The Local Field construction uses the eval Qpow sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L45-L46

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.evalQpow_sum {ι : Type*} (t : Finset ι) (P : ι → LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (∑ i ∈ t, P i) s = ∑ i ∈ t, evalQpow K (P i) s := by sorry
