-- Prove2me | Theorems.Thm_GroundTheory_Global_divisorSum_mul
-- name    : GroundTheory.Global.divisorSum_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:49:21.216086+00:00
-- url     : https://prove2.me/theorems/e608e092-f0f8-4212-b98b-18aea710e204
-- title:
--   Global: divisor Sum mul
-- statement:
--   The Global construction uses the divisor Sum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L66-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L66-L94

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

theorem GroundTheory.Global.divisorSum_mul {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    {I J : Ideal (𝓞 K)} (hIJ : I ⊔ J = ⊤) : divisorSum ψ (I * J) = divisorSum ψ I * divisorSum ψ J := by sorry
