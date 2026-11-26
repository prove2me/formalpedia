-- Prove2me | Theorems.Thm_FriedCrossing_Saturation_eigenvalue_eq_of_saturated
-- name    : FriedCrossing.Saturation.eigenvalue_eq_of_saturated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:56:22.838842+00:00
-- url     : https://prove2.me/theorems/5815745d-1440-5ac9-ae65-51def71a356d
-- title:
--   Saturation: eigenvalue eq of saturated
-- statement:
--   SATURATION: under the same hypotheses every eigenvalue of T equals s — there is no third
--   resonance in the disc.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L364-L374
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L364-L374

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.Saturation
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem FriedCrossing.Saturation.eigenvalue_eq_of_saturated (hdim : Module.finrank K V = 2) (T : V →ₗ[K] V) (s : K)
    (v₁ v₂ : V) (hind : LinearIndependent K ![v₁, v₂])
    (h₁ : T v₁ = s • v₁) (h₂ : T v₂ = s • v₂)
    {μ : K} {v : V} (hv : v ≠ 0) (hμ : T v = μ • v) : μ = s := by sorry
