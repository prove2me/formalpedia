-- Prove2me | Theorems.Thm_GenEmpLik_Expansion_lemma_7
-- name    : GenEmpLik.Expansion.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:01:52.812138+00:00
-- url     : https://prove2.me/theorems/fa610af3-2bb5-4434-94b2-a868f7bc68d6
-- title:
--   Lemma 7 — for identically distributed $Z_i$ with $E|Z_1|^k<\infty$, $\max_{i\le n}|Z_i|/n^{1/k}\to0$ almost surely
-- statement:
--   Let $Z_1,Z_2,\dots$ be identically distributed real random variables, not necessarily independent, with $E[|Z_1|^k]<\infty$ for some $k>0$. Then
--
--   1. for every $\epsilon>0$,
--   $$
--   \mathbb P\big(|Z_n|\ge\epsilon n^{1/k}\ \text{infinitely often}\big)=0;
--   $$
--   2. almost surely,
--   $$
--   \frac{\max_{i\le n}|Z_i|}{n^{1/k}}\to0 .
--   $$
--
--   With $k=2$ this shows that a finite-variance stationary sequence has no single observation of order $\sqrt n$, which makes the event of Lemma 6 hold eventually.
--
--   **Formalization Note** Lean indexes the sequence from $0$: `Z m` is the paper's $Z_{m+1}$, so the event of clause 1 is $|Z_m|\ge\epsilon(m+1)^{1/k}$, and the maximum in clause 2 is over the first $n$ variables `Z 0, …, Z (n-1)`. "Infinitely often" is `Filter.limsup` of the events along `atTop`. Identical distribution is Mathlib's `IdentDistrib`; no independence is assumed. Powers with real exponent are `Real.rpow`.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 31, Lemma 7

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace GenEmpLik.Expansion

/-- Lemma 7 (Duchi, Glynn & Namkoong, arXiv:1610.03425v3, p. 31). Let `Z 0, Z 1, …` (the paper's
`Z₁, Z₂, …`) be identically distributed, possibly dependent, with `E[|Z₁|^k] < ∞` for some `k > 0`.
Then for every `ε > 0`, `P(|Z_n| ≥ ε n^{1/k} i.o.) = 0` (Lean's `Z m` is the paper's `Z_{m+1}`,
so the threshold is `ε (m+1)^{1/k}`), and `max_{i ≤ n} |Z_i| / n^{1/k} → 0` almost surely. -/
theorem lemma_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) {k : ℝ} (hk : 0 < k)
    (hmom : Integrable (fun ω => |Z 0 ω| ^ k) P) :
    (∀ ε : ℝ, 0 < ε →
      P (limsup (fun m : ℕ => {ω | ε * ((m : ℝ) + 1) ^ (1 / k) ≤ |Z m ω|}) atTop) = 0) ∧
    (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (⨆ i : Fin n, |Z i ω|) / (n : ℝ) ^ (1 / k))
      atTop (𝓝 0)) := by sorry

end GenEmpLik.Expansion
