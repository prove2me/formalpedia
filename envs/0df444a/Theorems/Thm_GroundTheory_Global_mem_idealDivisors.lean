-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_idealDivisors
-- name    : GroundTheory.Global.mem_idealDivisors
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:31.735601+00:00
-- url     : https://prove2.me/theorems/85cacd09-d420-4b98-93a9-c6de5e91f6e1
-- title:
--   Global: mem ideal Divisors
-- statement:
--   The Global construction uses the mem ideal Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L24-L26

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

theorem GroundTheory.Global.mem_idealDivisors {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) : J ∈ idealDivisors I ↔ I ≤ J := by sorry
