-- Prove2me | Theorems.Thm_LocalDensityLSH_Count_chernoff_half_fail
-- name    : LocalDensityLSH.Count.chernoff_half_fail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:23:00.049882+00:00
-- url     : https://prove2.me/theorems/42a7b4e9-e581-4af3-aeab-c00edf5fa26e
-- title:
--   §5, p. 16, Chernoff step — ℙ(F ≥ M/2) ≤ e^{−(2 ln 2−1)M/4} ≤ e^{−M/11} for M independent failures of probability ≤ 1/4
-- statement:
--   Let $F_1,\dots,F_M$ be mutually independent events on a probability space, each with $\mathbb P(F_m)\le 1/4$, and let $F=\sum_{m=1}^M\mathbb 1_{F_m}$ be the number of them that occur. Then
--   $$\mathbb P\left(F\ge\frac M2\right)\ \le\ e^{-(2\ln2-1)M/4}\ \le\ e^{-M/11}.$$
--
--   Applied to the failure events of $M$ independent estimators, this is the probabilistic half of the median-of-means argument: $M\ge 11\ln(1/\delta)$ estimators suffice for failure probability $\delta$.
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, §5, p. 16 (Chernoff bound)

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model
import Definitions.Def_LocalDensityLSH_Count_Estimator

namespace LocalDensityLSH.Count

open MeasureTheory ProbabilityTheory

/-- §5, p. 16 (Chernoff step): for `M` independent events `F_m`, each of probability at most `1/4`,
the probability that at least `M/2` of them occur, i.e. that
`F = Σ_m 𝟙_{F_m} ≥ M/2`, is at most `e^{−(2 ln 2 − 1)M/4} ≤ e^{−M/11}`. -/
theorem chernoff_half_fail {M : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Fin M → Set Ω) (hF : ∀ m, MeasurableSet (F m))
    (hind : iIndepSet F P) (h14 : ∀ m, P.real (F m) ≤ 1 / 4) :
    P.real {ω | (M : ℝ) / 2 ≤ ∑ m, (F m).indicator (fun _ => (1 : ℝ)) ω} ≤
        Real.exp (-(2 * Real.log 2 - 1) * M / 4) ∧
      Real.exp (-(2 * Real.log 2 - 1) * M / 4) ≤ Real.exp (-(M : ℝ) / 11) := by sorry

end LocalDensityLSH.Count
