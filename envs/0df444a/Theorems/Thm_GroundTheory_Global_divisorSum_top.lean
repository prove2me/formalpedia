-- Prove2me | Theorems.Thm_GroundTheory_Global_divisorSum_top
-- name    : GroundTheory.Global.divisorSum_top
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:22.832522+00:00
-- url     : https://prove2.me/theorems/94e061c6-103d-5763-8b37-5f05ae9c4677
-- title:
--   Global: divisor Sum top
-- statement:
--   The Global construction uses the divisor Sum top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L39-L43

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

theorem GroundTheory.Global.divisorSum_top (ψ : Ideal (𝓞 K) → ℝ) : divisorSum ψ ⊤ = ψ ⊤ := by sorry
