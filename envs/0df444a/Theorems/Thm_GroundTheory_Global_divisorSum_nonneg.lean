-- Prove2me | Theorems.Thm_GroundTheory_Global_divisorSum_nonneg
-- name    : GroundTheory.Global.divisorSum_nonneg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:27.61684+00:00
-- url     : https://prove2.me/theorems/e1d14d02-d10e-4771-94f7-bce4a615b766
-- title:
--   Global: divisor Sum nonneg
-- statement:
--   The Global construction uses the divisor Sum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L129-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L129-L146

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

theorem GroundTheory.Global.divisorSum_nonneg {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    (hψ1 : ψ ⊤ = 1) (hψb : ∀ A, |ψ A| ≤ 1) (I : Ideal (𝓞 K)) : 0 ≤ divisorSum ψ I := by sorry
