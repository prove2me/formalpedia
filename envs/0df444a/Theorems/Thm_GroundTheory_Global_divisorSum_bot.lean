-- Prove2me | Theorems.Thm_GroundTheory_Global_divisorSum_bot
-- name    : GroundTheory.Global.divisorSum_bot
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:48:09.24123+00:00
-- url     : https://prove2.me/theorems/85b509d6-3cac-50d6-b389-1bf541544f26
-- title:
--   Global: divisor Sum bot
-- statement:
--   The Global construction uses the divisor Sum bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L36-L37

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

theorem GroundTheory.Global.divisorSum_bot (ψ : Ideal (𝓞 K) → ℝ) : divisorSum ψ ⊥ = 0 := by sorry
