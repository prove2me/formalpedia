-- Prove2me | Theorems.Thm_FoundationsRL_TailBounds_lemma_36
-- name    : FoundationsRL.TailBounds.lemma_36
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:27.163712+00:00
-- url     : https://prove2.me/theorems/cd2b1062-9ffc-445d-a063-f671c82de08e
-- title:
--   Lemma 36 — multiplicative Freedman bounds for nonnegative bounded sequences
-- statement:
--   Let $(X_t)_{t\le T}$ be random variables adapted to a filtration $(\mathcal F_t)_{t\le T}$, write $\mathbb E_{t-1}[\cdot]=\mathbb E[\cdot\mid\mathcal F_{t-1}]$, and suppose $0\le X_t\le R$ almost surely. Then for every $\delta>0$, with probability at least $1-\delta$, both
--   $$
--   \sum_{t=1}^{T}X_t\le\frac32\sum_{t=1}^{T}\mathbb E_{t-1}[X_t]+4R\log(2\delta^{-1})
--   $$
--   and
--   $$
--   \sum_{t=1}^{T}\mathbb E_{t-1}[X_t]\le2\sum_{t=1}^{T}X_t+8R\log(2\delta^{-1})
--   $$
--   hold.
--
--   The two inequalities say that, up to constant factors and an additive $R\log(1/\delta)$, a sum of nonnegative bounded adapted variables and the sum of their conditional means are interchangeable. This is how in-sample estimation errors along a trajectory are converted into the conditional (on-policy) errors that regret bounds need, and back.
--
--   **Formalization Note** Conditional expectations are Mathlib's `condExp`; each $X_t$ is bounded and $\mathcal F_t$-measurable, hence integrable. Both inequalities are required on one event of probability at least $1-\delta$.
--
--   Differences from the source:
--   - encoding: a filtration (F_t)_{t≤T} and an adapted sequence (X_t)_{t≤T} → a filtration indexed by ℕ, with X_t F_t-measurable for 1 ≤ t ≤ T and F_0 = ℱ 0; reason: a finite filtration extends by F_t = F_T for t > T, and values of X outside 1..T do not enter; same instances
--   - encoding: δ ∈ (0, 1), implicit → δ > 0; reason: for δ ≥ 1 the probability bound 1 − δ ≤ 0 is trivial; only δ ≤ 0, where log(δ⁻¹) is undefined, is excluded
--   - reading: 0 ≤ X_t ≤ R almost surely (R ≥ 0 presupposed) → explicit hypothesis 0 ≤ R; reason: for T ≥ 1 it follows from 0 ≤ X_t ≤ R, so no instance with T ≥ 1 is excluded; at T = 0 the bound on X_t is vacuous and a negative R would make the claim false (0 ≤ 4R log(2/δ) fails for δ < 1)
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 36, p. 157

import Mathlib
open MeasureTheory ProbabilityTheory

namespace FoundationsRL.TailBounds

/-- **Lemma 36** (multiplicative Freedman for nonnegative sequences). Let `(X_t)_{t ≤ T}` be a
sequence of random variables adapted to a filtration `(F_t)_{t ≤ T}`. If `0 ≤ X_t ≤ R` almost
surely, then with probability at least `1 − δ`,
`∑_{t=1}^T X_t ≤ (3/2) ∑_{t=1}^T E_{t−1}[X_t] + 4R log(2δ⁻¹)` and
`∑_{t=1}^T E_{t−1}[X_t] ≤ 2 ∑_{t=1}^T X_t + 8R log(2δ⁻¹)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Lemma 36, p. 157.

**Formalization Note.** `E_{t−1}[·]` is the conditional expectation `μ[· | ℱ (t − 1)]` given
`F_{t−1}`; bounded and `F_t`-measurable, each `X_t` is integrable. Both inequalities hold on one
event of probability at least `1 − δ`. Only `X_t` for `1 ≤ t ≤ T` enter. `0 ≤ R` is stated
as a hypothesis: the page's `0 ≤ X_t ≤ R` presupposes it, and at `T = 0` (where the bound on
`X_t` is vacuous) a negative `R` would make the right sides negative. `δ > 0` is the only
restriction on `δ`. -/
theorem lemma_36 {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (T : ℕ) (X : ℕ → Ω → ℝ)
    (hX : ∀ t ∈ Finset.Icc 1 T, StronglyMeasurable[ℱ t] (X t))
    (R : ℝ) (hR : 0 ≤ R) (hbdd : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂μ, 0 ≤ X t ω ∧ X t ω ≤ R)
    (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ μ.real {ω |
        ∑ t ∈ Finset.Icc 1 T, X t ω ≤
            3 / 2 * ∑ t ∈ Finset.Icc 1 T, (μ[X t | ℱ (t - 1)]) ω + 4 * R * Real.log (2 * δ⁻¹) ∧
        ∑ t ∈ Finset.Icc 1 T, (μ[X t | ℱ (t - 1)]) ω ≤
            2 * ∑ t ∈ Finset.Icc 1 T, X t ω + 8 * R * Real.log (2 * δ⁻¹)} := by sorry

end FoundationsRL.TailBounds
