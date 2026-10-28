-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeals_pairwise_comaximal
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_pairwise_comaximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:12:19.079762+00:00
-- url     : https://prove2.me/theorems/0e6f95ca-d2b9-4501-875d-976e02927322
-- title:
--   Distinct logarithmic center ideals are pairwise comaximal
-- statement:
--   For positive logarithmic dimension, coordinatewise injectivity makes distinct centers differ in some coordinate. The corresponding generators differ by a nonzero constant, which yields comaximality of the ideals they generate, including the unit-ideal exponent boundary. This removes the center-separation algebra from the parent. A proof route is to choose a coordinate using `m ≥ 1`, apply injectivity to the distinct indices, use the difference of the logarithmic coordinates to obtain a unit in the sum of the powered-generator ideals, and lift that to the full center ideals.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_pairwise_comaximal
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (e : Fin (m + 1) → Nat) :
    ∀ j k : Fin K, j ≠ k →
      IsCoprime
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e)
        (logarithmicCenterIdeal (c k) (fun _ => e 0) e) := by sorry
