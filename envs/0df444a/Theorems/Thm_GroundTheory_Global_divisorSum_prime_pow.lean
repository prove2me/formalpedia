-- Prove2me | Theorems.Thm_GroundTheory_Global_divisorSum_prime_pow
-- name    : GroundTheory.Global.divisorSum_prime_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:44.024803+00:00
-- url     : https://prove2.me/theorems/da0a9a9c-2f83-5df7-88fd-6b7a89958eb9
-- title:
--   Global: divisor Sum prime pow
-- statement:
--   The Global construction uses the divisor Sum prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L96-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L96-L117

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

theorem GroundTheory.Global.divisorSum_prime_pow {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    (hψ1 : ψ ⊤ = 1) {P : Ideal (𝓞 K)} (hP : Prime P) (k : ℕ) :
    divisorSum ψ (P ^ k) = ∑ j ∈ Finset.range (k + 1), ψ P ^ j := by sorry
