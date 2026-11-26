-- Prove2me | Theorems.Thm_LefebvreVariations_cramer_rademacher_threshold_half
-- name    : LefebvreVariations.cramer_rademacher_threshold_half
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:26:14.482709+00:00
-- url     : https://prove2.me/theorems/8182d8dc-d39f-573b-9cbd-c772224b65bb
-- title:
--   Lefebvre's variations: for fair signs, the exponential decay rate of P(S_n >= n/2) is (3/4)log(3/2)+(1/4)log(1/2) in absolute value
-- statement:
--   Let $X_0,X_1,\dots$ be i.i.d. with $\mathbb{P}(X_0=1)=\mathbb{P}(X_0=-1)=\tfrac12$. Then
--   $$\lim_{n\to\infty}\frac1n\log\mathbb{P}\bigl(X_0+\dots+X_{n-1}\ge \tfrac n2\bigr)=-\Bigl(\tfrac34\log\tfrac32+\tfrac14\log\tfrac12\Bigr)\approx-0.1308 .$$
--
--   Here $\Lambda(t)=\log\cosh t$ and the rate $\sup_t\bigl(t/2-\log\cosh t\bigr)$ equals $\tfrac34\log\tfrac32+\tfrac14\log\tfrac12$, the relative entropy of a coin of bias $3/4$ with respect to a fair coin.
--
--   **Formalization Note** Statement in the setting of `LargeDeviations.cramer_theorem_real`: `X : ℕ → Ω → ℝ` measurable, `iIndepFun X P`, identically distributed (`IdentDistrib (X i) (X 0) P P`). Here `X 0` takes the values `1` and `-1` with probability `1/2` each (stated as `P {X 0 = 1} = 1/2` and `P {X 0 = -1} = 1/2`). The quantity is `(1/n) * Real.log (P {ω | n * a ≤ ∑_{i<n} X i ω}).toReal` with `a = 1/2`; at `n = 0` the term is `0`, which does not affect the limit. The parent's hypotheses (finite moment generating function, `E[X 0] < a`, `P (X 0 > a) > 0`) hold here and are not repeated.
--
--   **Why this is a variation.** Variation of the open platform problem LargeDeviations.cramer_theorem_real (Cramer's theorem for the half-line [na, infinity)). It is the first explicit case: fair +-1 steps at the threshold a=1/2, where the rate sup_t(t/2-log cosh t) is a binary relative entropy; it is the parent with the supremum evaluated, hence a consequence of the parent. A different Cramer theorem with strict threshold and an extended-real conclusion is already Proved on the platform (KellyStochasticNetworks.EffectiveBandwidth.cramer); this statement is the non-strict, real-valued form of the parent, with an explicit constant.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: LargeDeviations.cramer_theorem_real (platform, Open), whose source field cites H. Cramer, Actualites Scientifiques et Industrielles 736 (1938) 5-23, and Dembo-Zeitouni, Large Deviations Techniques and Applications, 2nd ed., Thm 2.2.3 (theorem number taken from the parent's source field, not independently verified; cited from memory). The value is the Legendre transform of log cosh at 1/2, i.e. the binary relative entropy KL(3/4 || 1/2) = (3/4)log(3/2)+(1/4)log(1/2) in absolute value = 0.130812. Numerical check in python3 with exact binomial tails: (1/n)log P(S_n>=n/2) is -0.13751 at n=400, -0.13177 at n=4000, -0.130936 at n=40000, -0.130827 at n=400000.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open MeasureTheory ProbabilityTheory Filter Topology

/-- Cramér's theorem for fair `±1` signs and the threshold `a = 1/2`: the rate is
`I(1/2) = (3/4) log (3/2) + (1/4) log (1/2) ≈ 0.1308`, the Legendre transform of `log cosh`. This is the
instance of `LargeDeviations.cramer_theorem_real` in which `X 0` is a fair sign.
Source: Cramér (1938); Dembo–Zeitouni, *Large Deviations Techniques and Applications*, Thm 2.2.3 (cited from memory). -/
theorem cramer_rademacher_threshold_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hp : P {ω | X 0 ω = 1} = 1 / 2) (hm : P {ω | X 0 ω = -1} = 1 / 2) :
    Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) *
        Real.log ((P {ω | (n : ℝ) * (1 / 2 : ℝ) ≤ ∑ i ∈ Finset.range n, X i ω}).toReal))
      atTop (𝓝 (-((3 / 4) * Real.log (3 / 2) + (1 / 4) * Real.log (1 / 2)))) := by
  sorry

end LefebvreVariations
