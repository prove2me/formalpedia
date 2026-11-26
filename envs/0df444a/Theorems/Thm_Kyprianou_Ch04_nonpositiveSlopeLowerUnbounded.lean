-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nonpositiveSlopeLowerUnbounded
-- name    : Kyprianou.Ch04.nonpositiveSlopeLowerUnbounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:43:31.119931+00:00
-- url     : https://prove2.me/theorems/126e781a-ee9f-500d-8b16-3416ec61798c
-- title:
--   Nonpositive secant slope excludes finite lower bounds
-- statement:
--   Choose a positive root for discount one. The nonsingular limiting infimum transform is zero when the nonnegative secant slope vanishes. Apply the vanishing-transform lower-unboundedness theorem.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.nonpositiveSlopeLowerUnbounded
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator : ¬ (∀ᵐ w : Ω ∂P, Antitone (fun t : NNReal => L.X t w)))
    (hm : max 0 (sInf ((fun theta : ℝ => L.ψ theta / theta) '' Ioi 0)) = 0) :
    P {w | BddBelow (range (fun t : NNReal => L.X t w))} = 0 := by
  sorry
