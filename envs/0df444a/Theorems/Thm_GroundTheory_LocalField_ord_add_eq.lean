-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ord_add_eq
-- name    : GroundTheory.LocalField.ord_add_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:34:34.314814+00:00
-- url     : https://prove2.me/theorems/fec2270d-fe06-45c2-8b32-efdaf98c3eb0
-- title:
--   Local Field: ord add eq
-- statement:
--   The Local Field construction uses the ord add eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L177-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L177-L188

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
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
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.ord_add_eq {x d : K} (hx : x ≠ 0) (hd : d ∈ valBall K (ord x + 1)) :
    x + d ≠ 0 ∧ ord (x + d) = ord x := by sorry
