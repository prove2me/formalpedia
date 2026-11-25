-- Prove2me | Theorems.Thm_GroundTheory_Global_hasSum_LSeries_term_divisorSum
-- name    : GroundTheory.Global.hasSum_LSeries_term_divisorSum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:57:32.964591+00:00
-- url     : https://prove2.me/theorems/841b7ca4-0b3f-407c-9c82-4d1d8ac96a81
-- title:
--   Global: has Sum LSeries term divisor Sum
-- statement:
--   The Global construction uses the has Sum LSeries term divisor Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L226-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L226-L247

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

theorem GroundTheory.Global.hasSum_LSeries_term_divisorSum {ψ : Ideal (𝓞 K) → ℝ} (hψb : ∀ A, |ψ A| ≤ 1) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (LSeries.term (divisorSumCoeff ψ) s)
      ((∑' J, (ψ J : ℂ) * (absNorm J : ℂ) ^ (-s)) * dedekindZeta K s) := by sorry
