-- Prove2me | Theorems.Thm_GroundTheory_Global_geom_sum_nonneg_of_abs_le_one
-- name    : GroundTheory.Global.geom_sum_nonneg_of_abs_le_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:25.9248+00:00
-- url     : https://prove2.me/theorems/102cca9d-d7e2-516f-83d2-40017029fd69
-- title:
--   Global: geom sum nonneg of abs le one
-- statement:
--   The Global construction uses the geom sum nonneg of abs le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L119-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L119-L127

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NonvanishingDivisorSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Complex Filter Topology
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.geom_sum_nonneg_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    0 ≤ ∑ j ∈ Finset.range n, x ^ j := by sorry
