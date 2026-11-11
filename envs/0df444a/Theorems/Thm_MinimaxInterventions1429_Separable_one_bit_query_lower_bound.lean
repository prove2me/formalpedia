-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_one_bit_query_lower_bound
-- name    : MinimaxInterventions1429.Separable.one_bit_query_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:50.717066+00:00
-- url     : https://prove2.me/theorems/cfb6b0ae-5591-46d6-88cc-fb7c5efdcce9
-- title:
--   Proposition 4.3 — one-bit query lower bound
-- statement:
--   Let $m,k\ge2$ and $0<\gamma\le1/128$. Consider any possibly randomized adaptive one-bit algorithm, with an arbitrary probability space of private random seeds, whose number of calls is at most the natural number $Q$ on every branch. Suppose that for every table $L\in[0,1]^{m\times k}$ with $\Lambda(L)\ge1/8$ and every exact bit oracle for $L$, the algorithm returns a real table $\widehat L$ with $d_q(\widehat L,L)\le\gamma$ with probability at least $2/3$. Then
--
--   $$Q\ge(mk-1)\log_2\!\frac1{128\gamma}-\log_2\!\frac32.$$
--
--   Queries can have arbitrary real surcharge entries and be fully adaptive; output failure is not a success. The probability is over the algorithm's seed, exact bit kernels and their relevant success events are measurable, and the logarithmic bound is a real inequality, not an integer-rounded substitute. This lower bound applies to the exact-answer regime without finite-support or rational-query assumptions.
--
--   Differences from the source:
--   - encoding: rows and actions indexed from 1 with m,k ≥ 2 → Fin m and Fin k, source column 1 represented by 0, with explicit 2 ≤ m and 2 ≤ k; reason: order-preserving relabeling; closed-simplex mixtures and arbitrary real arrays retain every source instance
--   - encoding: minimum of F on the closed simplex and quotient distance defined by an infimum over scalar shifts → optimality compared against every simplex point and quotient distance equal to half the oscillation; reason: the finite nonempty simplex is compact and the objective continuous; Eq. (2) gives the identical quotient distance without default-valued infima
--   - encoding: possibly randomized procedures, with all events and transcripts measurable → arbitrary probability spaces for random seeds, measurable common response maps and exact bit kernels, and explicit measurable output or success-event conditions; probabilities in ENNReal; reason: these are Section 2 standing measurability conventions, not restrictions to finite seeds, rational queries or fixed tie-breaking
--   - generalization: the baseline query family in Section 2 is bounded and separable → the query program may use arbitrary real surcharge matrices; reason: the source packing and binary-tree counting proof does not use any intervention restriction; restricting queries recovers the baseline result
--   - encoding: real base-two logarithmic bound on the natural query budget Q → Q cast to the reals and log x divided by log 2; reason: gamma is positive and at most 1/128, so all logarithms and divisions have the source domain
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Proposition 4.3, printed p.15 (PDF p.17)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

namespace MinimaxInterventions1429.Separable

theorem one_bit_query_lower_bound {m k : ℕ} [NeZero m] [NeZero k]
    (hm : 2 ≤ m) (hk : 2 ≤ k) (γ : ℝ) (hγ : 0 < γ) (hγu : γ ≤ 1 / 128)
    (Q : ℕ) {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (A : Ω → BitProgram m k (Option (Table m k)))
    (hQ : ∀ s, (A s).maxQueries ≤ Q)
    (hmeas : ∀ (L : Table m k) (O : BitOracle m k),
      ExactOracle L O → MeasurableSet {s | Within L γ ((A s).run O []).1})
    (hacc : ∀ L : Table m k, InCube L → (1 : ℝ) / 8 ≤ interaction L →
      ∀ O : BitOracle m k, ExactOracle L O →
        (2 / 3 : ENNReal) ≤ μ {s | Within L γ ((A s).run O []).1}) :
    ((m * k - 1 : ℕ) : ℝ) * (Real.log (1 / (128 * γ)) / Real.log 2) -
      Real.log ((3 : ℝ) / 2) / Real.log 2 ≤ (Q : ℝ) := by sorry

end MinimaxInterventions1429.Separable
