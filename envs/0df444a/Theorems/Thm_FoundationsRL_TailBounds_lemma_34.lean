-- Prove2me | Theorems.Thm_FoundationsRL_TailBounds_lemma_34
-- name    : FoundationsRL.TailBounds.lemma_34
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:22.270307+00:00
-- url     : https://prove2.me/theorems/238b4a6c-6090-4a55-9a31-142e4448fd16
-- title:
--   Lemma 34 — time-uniform exponential (Chernoff–Ville) bound for adapted sequences
-- statement:
--   Let $(X_t)_{t\le T}$ be real random variables adapted to a filtration $(\mathcal F_t)_{t\le T}$, and write $\mathbb E_{t-1}[\cdot]=\mathbb E[\cdot\mid\mathcal F_{t-1}]$. For every $\delta>0$, with probability at least $1-\delta$, simultaneously for all $T'\le T$,
--   $$
--   \sum_{t=1}^{T'}X_t\le\sum_{t=1}^{T'}\log\big(\mathbb E_{t-1}[e^{X_t}]\big)+\log(\delta^{-1}).\qquad\text{(A.3)}
--   $$
--
--   No boundedness or integrability is assumed: a conditional exponential moment may be $+\infty$, in which case the right side is $+\infty$. This inequality is the common source of the martingale tail bounds of the appendix, among them Freedman's inequality (Lemma 35).
--
--   **Formalization Note** $\mathbb E_{t-1}[e^{X_t}]$ is the conditional Lebesgue expectation of the nonnegative variable $e^{X_t}$ (Mathlib's `condLExp`), valued in $[0,\infty]$, and its logarithm is `ENNReal.log`, with $\log\infty=\infty$; the inequality is between extended reals. Since $e^{X_t}>0$, the conditional expectation is positive almost surely, so the value $-\infty$ occurs only on a null set. $T'=0$ (empty sums) is included.
--
--   Differences from the source:
--   - encoding: a filtration (F_t)_{t≤T} and an adapted sequence (X_t)_{t≤T} → a filtration indexed by ℕ, with X_t F_t-measurable for 1 ≤ t ≤ T and F_0 = ℱ 0; reason: a finite filtration extends by F_t = F_T for t > T, and values of X outside 1..T do not enter; same instances
--   - encoding: E_{t−1}[e^{X_t}] and its logarithm, with no integrability assumed → the conditional Lebesgue expectation condLExp in [0, ∞], ENNReal.log in [−∞, ∞], the inequality in EReal; reason: a conditional expectation of a nonnegative, possibly non-integrable variable takes values in [0, ∞]; log ∞ = ∞ makes the bound trivial there, as in the source; −∞ occurs only on a null set
--   - encoding: δ ∈ (0, 1), implicit → δ > 0; reason: for δ ≥ 1 the probability bound 1 − δ ≤ 0 is trivial; only δ ≤ 0, where log(δ⁻¹) is undefined, is excluded
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 34, (A.3), p. 156

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FoundationsRL.TailBounds

/-- **Lemma 34.** For any sequence of real-valued random variables `(X_t)_{t ≤ T}` adapted to a
filtration `(F_t)_{t ≤ T}`, with probability at least `1 − δ`, for all `T′ ≤ T`,
`∑_{t=1}^{T′} X_t ≤ ∑_{t=1}^{T′} log(E_{t−1}[e^{X_t}]) + log(δ⁻¹)` (A.3).
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Lemma 34, (A.3), p. 156.

**Formalization Note.** `E_{t−1}[·]` is the conditional expectation given `F_{t−1} = ℱ (t − 1)`.
Since the notes assume no integrability, `E_{t−1}[e^{X_t}]` is Mathlib's conditional *Lebesgue*
expectation `condLExp` of the nonnegative function `e^{X_t}`, valued in `[0, ∞]`, and its logarithm
is `ENNReal.log`, valued in `[−∞, ∞]` (`log ∞ = ∞`); the inequality is in `EReal`. The value `−∞`
(where `condLExp` vanishes) occurs only on a null set, because `e^{X_t} > 0`. Only `X_t` for
`1 ≤ t ≤ T` enter, and only they are required to be adapted. `T′ = 0` is included (empty sums). -/
theorem lemma_34 {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (T : ℕ) (X : ℕ → Ω → ℝ)
    (hX : ∀ t ∈ Finset.Icc 1 T, StronglyMeasurable[ℱ t] (X t))
    (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ μ.real {ω | ∀ T' ≤ T,
        ((∑ t ∈ Finset.Icc 1 T', X t ω : ℝ) : EReal) ≤
          (∑ t ∈ Finset.Icc 1 T',
              ENNReal.log (condLExp (ℱ (t - 1)) μ (fun ω' => ENNReal.ofReal (Real.exp (X t ω'))) ω))
            + ((Real.log δ⁻¹ : ℝ) : EReal)} := by sorry

end FoundationsRL.TailBounds
