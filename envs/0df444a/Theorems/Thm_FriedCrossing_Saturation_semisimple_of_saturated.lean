-- Prove2me | Theorems.Thm_FriedCrossing_Saturation_semisimple_of_saturated
-- name    : FriedCrossing.Saturation.semisimple_of_saturated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:56:26.455288+00:00
-- url     : https://prove2.me/theorems/632bb24f-83df-57e3-bf9b-181408281f1e
-- title:
--   Saturation: semisimple of saturated
-- statement:
--   No Jordan block: (T − s)² = 0 already at the first power, so algebraic multiplicity of s
--   is exactly the rank 2 = its geometric multiplicity (SEMISIMPLE double point — the premise
--   `M(θ,0) = s*·1` of §2).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L379-L383
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L379-L383

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.Saturation
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem FriedCrossing.Saturation.semisimple_of_saturated (hdim : Module.finrank K V = 2) (T : V →ₗ[K] V) (s : K)
    (v₁ v₂ : V) (hind : LinearIndependent K ![v₁, v₂])
    (h₁ : T v₁ = s • v₁) (h₂ : T v₂ = s • v₂) :
    T - s • LinearMap.id = 0 := by sorry
