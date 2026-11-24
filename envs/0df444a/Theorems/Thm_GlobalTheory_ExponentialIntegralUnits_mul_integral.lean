-- Prove2me | Theorems.Thm_GlobalTheory_ExponentialIntegralUnits_mul_integral
-- name    : GlobalTheory.ExponentialIntegralUnits.mul_integral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:15:40.756404+00:00
-- url     : https://prove2.me/theorems/9c884ffb-9195-43fb-bb71-85b53b35c5cc
-- title:
--   Exponential Integral Units: mul integral
-- statement:
--   The Exponential Integral Units construction uses the mul integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsUnitIntegral.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsUnitIntegral.lean#L29-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsUnitIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NormedSpace Filter Topology
open GlobalTheory GlobalTheory.ExponentialIntegralUnits
universe u_1
variable {𝔸 : Type u_1} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem GlobalTheory.ExponentialIntegralUnits.mul_integral (M : ℝ → 𝔸) (hc : Continuous M)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) (t δ : ℝ) :
    M t * (∫ s in (0 : ℝ)..δ, M s)
      = (∫ s in (0 : ℝ)..(t + δ), M s) - ∫ s in (0 : ℝ)..t, M s := by sorry
