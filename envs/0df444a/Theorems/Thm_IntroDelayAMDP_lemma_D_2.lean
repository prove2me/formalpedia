-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_D_2
-- name    : IntroDelayAMDP.lemma_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:48.541876+00:00
-- url     : https://prove2.me/theorems/1de7333f-c561-4df1-bb7b-a7b6cf73bcd5
-- title:
--   Lemma D.2 — lower-tail Freedman inequality
-- statement:
--   Let $X_k\ge0$ be square-integrable and adapted to $(\mathcal F_k)$. Then for every $\lambda>0$ and $\delta'\in(0,1)$, with probability at least $1-\delta'$,
--   $$\sum_{k=1}^KX_k\ge\sum_{k=1}^K\mathbb E_{k-1}[X_k]-\frac\lambda2\sum_{k=1}^K\mathbb E_{k-1}[X_k^2]-\frac{\log(1/\delta')}\lambda.$$
--   It is the lower-tail tool of Lemma A.14.
--
--   Differences from the source:
--   - encoding: with probability at least 1 − p → μ(failure set) ≤ p; reason: outer-measure bound on the failure set; no measurability side condition is needed
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma D.2, p.66

import Mathlib

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma D.2 (Lower-Tail Freedman Inequality)** (printed p.66, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "Let `X_k ≥ 0` be
square-integrable and adapted to `(F_k)`. Then, for every `λ > 0` and `δ′ ∈ (0, 1)`, with probability at
least `1 − δ′`, `∑_{k=1}^K X_k ≥ ∑_{k=1}^K E_{k−1}[X_k] − (λ/2)∑_{k=1}^K E_{k−1}[X_k²] − log(1/δ′)/λ`."

**Formalization Note.** A filtration `(F_k)_{k∈ℕ}`; sums over `k = 1, …, K`; `E_{k−1}` is the conditional
expectation given `F_{k−1}`; square integrability is `MemLp (X k) 2`. -/
theorem lemma_D_2 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (K : ℕ) (hXa : Adapted ℱ X)
    (hX0 : ∀ k ω, 0 ≤ X k ω) (hX2 : ∀ k, MemLp (X k) 2 μ) (lam δ' : ℝ) (hlam : 0 < lam)
    (hδ : 0 < δ') (hδ1 : δ' < 1) :
    μ {ω | ∑ k ∈ Finset.Icc 1 K, X k ω < ∑ k ∈ Finset.Icc 1 K, μ[X k | ℱ (k - 1)] ω -
        lam / 2 * ∑ k ∈ Finset.Icc 1 K, μ[(fun ω' => X k ω' ^ 2) | ℱ (k - 1)] ω -
        Real.log (1 / δ') / lam} ≤ ENNReal.ofReal δ' := by sorry

end IntroDelayAMDP
