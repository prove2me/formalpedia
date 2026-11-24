-- Prove2me | Theorems.Thm_GlobalTheory_ExponentialIntegralUnits_hasDerivAt_primitive
-- name    : GlobalTheory.ExponentialIntegralUnits.hasDerivAt_primitive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:58.646315+00:00
-- url     : https://prove2.me/theorems/bfbb594b-e1c0-432c-a1a6-8566ae136899
-- title:
--   Exponential Integral Units: has Deriv At primitive
-- statement:
--   The Exponential Integral Units construction uses the has Deriv At primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsUnitIntegral.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsUnitIntegral.lean#L11-L13

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

theorem GlobalTheory.ExponentialIntegralUnits.hasDerivAt_primitive (M : ℝ → 𝔸) (hc : Continuous M) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, M s) (M t) t := by sorry
