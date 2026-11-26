-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nonSingularInfimumTransform
-- name    : Kyprianou.Ch04.nonSingularInfimumTransform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:43:34.117838+00:00
-- url     : https://prove2.me/theorems/aca18d67-7035-4680-be94-9df2ac3699a2
-- title:
--   Nonsingular limiting running-infimum transform
-- statement:
--   The bounded monotone running-infimum means have a limit. Exponential-clock averaging tends to the same limit; the product-clock Wiener-Hopf formula and convex secant quotient identify it.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.nonSingularInfimumTransform
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator : ¬ (∀ᵐ w : Ω ∂P, Antitone (fun t : NNReal => L.X t w)))
    (beta : ℝ) (hb : 0 < beta) (hpsi : L.ψ beta ≠ 0) :
    Tendsto (fun t : NNReal => ∫ w, Real.exp (beta * sInf ((fun s : NNReal => L.X s w) '' Iic t)) ∂P)
      atTop (nhds (max 0 (sInf ((fun theta : ℝ => L.ψ theta / theta) '' Ioi 0)) * beta / L.ψ beta)) := by
  sorry
