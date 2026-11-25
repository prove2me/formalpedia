-- Prove2me | Theorems.Thm_GroundTheory_Global_summable_norm_mul_cpow
-- name    : GroundTheory.Global.summable_norm_mul_cpow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:48:21.66646+00:00
-- url     : https://prove2.me/theorems/957efe02-469a-5bcf-a2f4-4021a733d831
-- title:
--   Global: summable norm mul cpow
-- statement:
--   The Global construction uses the summable norm mul cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L153-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L153-L160

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

theorem GroundTheory.Global.summable_norm_mul_cpow {ψ : Ideal (𝓞 K) → ℝ} (hψb : ∀ A, |ψ A| ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : Summable fun J : Ideal (𝓞 K) ↦ ‖(ψ J : ℂ) * (absNorm J : ℂ) ^ (-s)‖ := by sorry
