-- Prove2me | Theorems.Thm_Kyprianou_Ch04_infimumLimitSupport
-- name    : Kyprianou.Ch04.infimumLimitSupport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:43:26.34744+00:00
-- url     : https://prove2.me/theorems/15502881-1f63-5400-a75a-ad78274acfbd
-- title:
--   Support and vanishing of limiting running-infimum means
-- statement:
--   Use integer horizons, cofinal in NNReal. The exponential reward infimum is positive exactly on lower-bounded paths, and bounded convergence identifies the expectation. This yields the support estimate and zero-mass limit.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.infimumLimitSupport
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (beta : ℝ) (hb : 0 < beta) :
    let B : Set Ω := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let f : NNReal → ℝ := fun t => ∫ w, Real.exp (beta * sInf ((fun s : NNReal => L.X s w) '' Iic t)) ∂P
    MeasurableSet B ∧
      (∀ ell : ℝ, Tendsto f atTop (nhds ell) → ell ≤ (P B).toReal) ∧
      (P B = 0 → Tendsto f atTop (nhds 0)) := by
  sorry
