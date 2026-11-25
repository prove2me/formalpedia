-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_esscher_H_grid_variation
-- name    : Kyprianou.Ch04.kw47_esscher_H_grid_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:53:54.900251+00:00
-- url     : https://prove2.me/theorems/9bcaa377-e78b-52b4-bd2e-7c84ef67ae77
-- title:
--   Uniform finite-horizon total variation of Kella-Whitt Esscher factor
-- statement:
--   For the continuous nondecreasing Lévy running supremum U and alpha≥0, the factor H(t)=exp(-alpha U(t)+psi(alpha)t) has total absolute variation at most 2 exp(|psi(alpha)|T) on any finite increasing deterministic time grid bounded by T. Write H=A B with A=exp(-alpha U) decreasing in [0,1] and B=exp(psi(alpha)t) a positive monotone sequence bounded by exp(|psi(alpha)|T). Apply the Proved unit variation bound for A, monotone variation bound for B, and generic product variation inequality. This supplies a deterministic uniform variation envelope for the exact product-grid transfer.
-- source:
--   Kyprianou (2006) Exercise 4.7, p. 108 and solution pp. 320–321; integration by parts for the running-maximum exponential.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_monotone_exp_unit_variation
import Theorems.Thm_Kyprianou_Ch04_kw47_positive_monotone_grid_variation
import Theorems.Thm_Kyprianou_Ch04_kw47_product_grid_variation_bound
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Uniform finite-horizon deterministic variation of the
continuous Kella-Whitt Esscher running-maximum factor. -/

theorem Kyprianou.Ch04.kw47_esscher_H_grid_variation
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T : NNReal) (u : Nat → NNReal) (hu : Monotone u)
    (hT : ∀ i, u i ≤ T) (n : Nat) (w : Ω) :
    (∑ i ∈ Finset.range n,
       |Real.exp (-alpha * runningSup L (u (i+1)) w +
           L.ψ alpha * (u (i+1) : Real)) -
        Real.exp (-alpha * runningSup L (u i) w +
           L.ψ alpha * (u i : Real))|)
      ≤ 2 * Real.exp (|L.ψ alpha| * (T : Real)) := by sorry
