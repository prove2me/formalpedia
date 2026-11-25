-- Prove2me | Theorems.Thm_GroundTheory_Global_neg_ne_zero_of_one_lt_re
-- name    : GroundTheory.Global.neg_ne_zero_of_one_lt_re
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:20.075419+00:00
-- url     : https://prove2.me/theorems/1be8dad3-43de-52b4-84ab-e45be6c0eaa4
-- title:
--   Global: neg ne zero of one lt re
-- statement:
--   The Global construction uses the neg ne zero of one lt re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L148-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L148-L151

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

theorem GroundTheory.Global.neg_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : -s ≠ 0 := by sorry
