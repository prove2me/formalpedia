-- Prove2me | Theorems.Thm_LefebvreVariations_cramer_gaussian_threshold_one
-- name    : LefebvreVariations.cramer_gaussian_threshold_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:26:33.867894+00:00
-- url     : https://prove2.me/theorems/71c3e412-90bf-4264-84bd-711a7163a849
-- title:
--   Lefebvre's variations: for standard Gaussian steps, the exponential decay rate of P(S_n >= n) is 1/2
-- statement:
--   Let $X_0,X_1,\dots$ be i.i.d. standard normal random variables. Then
--   $$\lim_{n\to\infty}\frac1n\log\mathbb{P}\bigl(X_0+\dots+X_{n-1}\ge n\bigr)=-\frac12 .$$
--
--   Here $\Lambda(t)=t^2/2$ and $\sup_t\bigl(t-t^2/2\bigr)=1/2$; equivalently $\mathbb{P}(S_n\ge n)=\mathbb{P}(N(0,1)\ge\sqrt n)$ decays like $e^{-n/2}$ up to polynomial factors.
--
--   **Formalization Note** Statement in the setting of `LargeDeviations.cramer_theorem_real`: `X : ℕ → Ω → ℝ` measurable, `iIndepFun X P`, identically distributed (`IdentDistrib (X i) (X 0) P P`). Here the law of `X 0` is `gaussianReal 0 1` (stated as `P.map (X 0) = gaussianReal 0 1`). The quantity is `(1/n) * Real.log (P {ω | n * a ≤ ∑_{i<n} X i ω}).toReal` with `a = 1`; at `n = 0` the term is `0`, which does not affect the limit. The parent's hypotheses (finite moment generating function, `E[X 0] < a`, `P (X 0 > a) > 0`) hold here and are not repeated.
--
--   **Why this is a variation.** Variation of the open platform problem LargeDeviations.cramer_theorem_real (Cramer's theorem for the half-line). It is the Gaussian case at threshold a=1, where Lambda(t)=t^2/2 and the rate is exactly 1/2; it is the parent with the supremum evaluated, hence a consequence of the parent. A different Cramer theorem with strict threshold and an extended-real conclusion is already Proved on the platform (KellyStochasticNetworks.EffectiveBandwidth.cramer); this is the non-strict, real-valued form with an explicit constant.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: LargeDeviations.cramer_theorem_real (platform, Open), whose source field cites H. Cramer, Actualites Scientifiques et Industrielles 736 (1938) 5-23, and Dembo-Zeitouni, Large Deviations Techniques and Applications, 2nd ed., Thm 2.2.3 (theorem number taken from the parent's source field, not independently verified; cited from memory). For N(0,1), Lambda(t)=t^2/2 and sup_t (t - t^2/2) = 1/2. Numerical check in python3 with the exact normal tail: (1/n)log P(N >= sqrt n) = -0.5323 at n=100, -0.5098 at n=400, -0.5048 at n=900, converging to -1/2.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open MeasureTheory ProbabilityTheory Filter Topology

/-- Cramér's theorem for standard Gaussian summands and the threshold `a = 1`: `Λ(t) = t²/2`, so the rate is
`I(1) = 1/2` and `(1/n) log P(X₀+⋯+X_{n-1} ≥ n) → -1/2`. This is the instance of `LargeDeviations.cramer_theorem_real`
in which `X 0` is standard normal.
Source: Cramér (1938); Dembo–Zeitouni, *Large Deviations Techniques and Applications*, Thm 2.2.3 (cited from memory). -/
theorem cramer_gaussian_threshold_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hlaw : P.map (X 0) = gaussianReal 0 1) :
    Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) *
        Real.log ((P {ω | (n : ℝ) * (1 : ℝ) ≤ ∑ i ∈ Finset.range n, X i ω}).toReal))
      atTop (𝓝 (-(1 / 2 : ℝ))) := by
  sorry

end LefebvreVariations
