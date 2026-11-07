-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_D_1
-- name    : IntroDelayAMDP.lemma_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:31.926197+00:00
-- url     : https://prove2.me/theorems/6ed3b988-46a7-4795-ba0a-aafbe9770103
-- title:
--   Lemma D.1 — multiplicative Freedman inequality
-- statement:
--   Let $X_k\in[0,R]$ be adapted to $(\mathcal F_k)$, and let $m_k\ge\mathbb E_{k-1}[X_k]$ be $\mathcal F_{k-1}$-measurable. Then for every $\delta'\in(0,1)$, with probability at least $1-\delta'$,
--   $$\sum_{k=1}^KX_k\le(e-1)\sum_{k=1}^Km_k+R\log\frac1{\delta'}.$$
--   It is the upper-tail concentration tool of Lemmas A.7 and A.11.
--
--   Differences from the source:
--   - encoding: with probability at least 1 − p → μ(failure set) ≤ p; reason: outer-measure bound on the failure set; no measurability side condition is needed
--   - encoding: m_k ≥ E_{k−1}[X_k] → the inequality holds almost surely; reason: conditional expectations are defined up to null sets
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma D.1, p.66

import Mathlib

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma D.1 (Multiplicative Freedman Inequality)** (printed p.66, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "Let `X_k ∈ [0, R]` be
adapted to `(F_k)`, and let `m_k ≥ E_{k−1}[X_k]` be `F_{k−1}`-measurable. Then, for every `δ′ ∈ (0, 1)`,
with probability at least `1 − δ′`, `∑_{k=1}^K X_k ≤ (e − 1)∑_{k=1}^K m_k + R log(1/δ′)`."

**Formalization Note.** A filtration `(F_k)_{k∈ℕ}` on a probability space; the sums run over
`k = 1, …, K`; `E_{k−1}[X_k]` is the conditional expectation given `F_{k−1}`, and `m_k ≥ E_{k−1}[X_k]`
holds almost surely. The failure probability is bounded by `δ′`. -/
theorem lemma_D_1 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X m : ℕ → Ω → ℝ) (R : ℝ) (K : ℕ) (hXa : Adapted ℱ X)
    (hX : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ R) (hm : ∀ k, 1 ≤ k → Measurable[ℱ (k - 1)] (m k))
    (hmX : ∀ k, 1 ≤ k → μ[X k | ℱ (k - 1)] ≤ᵐ[μ] m k) (δ' : ℝ) (hδ : 0 < δ') (hδ1 : δ' < 1) :
    μ {ω | (Real.exp 1 - 1) * ∑ k ∈ Finset.Icc 1 K, m k ω + R * Real.log (1 / δ') <
      ∑ k ∈ Finset.Icc 1 K, X k ω} ≤ ENNReal.ofReal δ' := by sorry

end IntroDelayAMDP
