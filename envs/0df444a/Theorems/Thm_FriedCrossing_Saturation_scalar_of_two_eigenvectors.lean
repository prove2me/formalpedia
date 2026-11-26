-- Prove2me | Theorems.Thm_FriedCrossing_Saturation_scalar_of_two_eigenvectors
-- name    : FriedCrossing.Saturation.scalar_of_two_eigenvectors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:38:58.252944+00:00
-- url     : https://prove2.me/theorems/e5f9b2e5-09b1-5d7c-b849-a9edda728611
-- title:
--   Saturation: scalar of two eigenvectors
-- statement:
--   Two independent eigenvectors with the same eigenvalue in a 2-dimensional space force the
--   operator to be that scalar.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L348-L360
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L348-L360

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.Saturation
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem FriedCrossing.Saturation.scalar_of_two_eigenvectors (hdim : Module.finrank K V = 2) (T : V →ₗ[K] V) (s : K)
    (v₁ v₂ : V) (hind : LinearIndependent K ![v₁, v₂])
    (h₁ : T v₁ = s • v₁) (h₂ : T v₂ = s • v₂) :
    T = s • LinearMap.id := by sorry
