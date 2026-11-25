-- Prove2me | Theorems.Thm_GroundTheory_Global_idealDivisors_bot
-- name    : GroundTheory.Global.idealDivisors_bot
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:48.7565+00:00
-- url     : https://prove2.me/theorems/13f04839-9aaa-4464-b51b-7d09901897eb
-- title:
--   Global: ideal Divisors bot
-- statement:
--   The Global construction uses the ideal Divisors bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L29-L30

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

theorem GroundTheory.Global.idealDivisors_bot : idealDivisors (⊥ : Ideal (𝓞 K)) = ∅ := by sorry
