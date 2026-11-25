-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ord_neg_eq
-- name    : GroundTheory.LocalField.ord_neg_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:30:17.114154+00:00
-- url     : https://prove2.me/theorems/d3a60f96-c4d1-5515-a587-7ad082af262d
-- title:
--   Local Field: ord neg eq
-- statement:
--   The Local Field construction uses the ord neg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L34-L35

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
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

theorem GroundTheory.LocalField.ord_neg_eq (x : K) : ord (-x) = ord x := by sorry
