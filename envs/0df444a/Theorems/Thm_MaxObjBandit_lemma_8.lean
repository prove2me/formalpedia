-- Prove2me | Theorems.Thm_MaxObjBandit_lemma_8
-- name    : MaxObjBandit.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:58.306225+00:00
-- url     : https://prove2.me/theorems/431d5eb2-e9ee-4617-8427-1a17af32e8eb
-- title:
--   Lemma 8 — anytime lower deviation of the empirical mean with a $\log^+(1/(\delta t^{3/2}))$ bonus
-- statement:
--   Let $\delta\in(0,1)$ and let $X_1,X_2,\dots$ be independent random variables, each $0$-mean and $1$-sub-Gaussian, with empirical means $\bar\mu_t=\frac1t\sum_{s=1}^tX_s$. Then for every $x>0$,
--   $$
--   P\Big(\exists\,t>0:\ \bar\mu_t+\sqrt{\frac4t\log^+\Big(\frac1{\delta t^{3/2}}\Big)}+x<0\Big)\le\frac{39\,\delta}{x^3}.
--   $$
--
--   The bound controls, uniformly over time, how far an upper confidence index with the time-varying confidence level $\delta t^{3/2}$ can fall below the true mean. With $\delta=K/T$ it gives the first term of (84).
--
--   **Formalization Note** $1$-sub-Gaussian is Mathlib's `HasSubgaussianMGF (X s) 1 P`, which also forces mean $0$; the variables need not be identically distributed. The probability is `P.real`.
--
--   Differences from the source:
--   - encoding: $X_1,X_2,\dots$ indexed from $1$, $\bar\mu_t=\frac1t\sum_{s=1}^tX_s$ → `X : ℕ → Ω → ℝ` indexed from $0$, $\bar\mu_t=(\sum_{s<t}X_s)/t$; reason: Lean indexing convention; the same sequence
-- source:
--   Ozbay, Kamble, Maximal Objectives in the Multi-armed Bandit with Applications, arXiv:2006.06853v6, Lemma 8, p.71

import Mathlib
import Definitions.Def_MaxObjBandit_BanditInstance

open MeasureTheory ProbabilityTheory

namespace MaxObjBandit

/-- **Lemma 8** (arXiv:2006.06853v6, Lemma 8, p.71). Let `δ ∈ (0,1)` and let `X₁, X₂, …` be
independent `0`-mean `1`-sub-Gaussian random variables, with `µ̄ₜ = (1/t) ∑_{s=1}^t X_s`. Then for
every `x > 0`,
`P(∃ t > 0 : µ̄ₜ + √((4/t) log⁺(1/(δ t^{3/2}))) + x < 0) ≤ 39δ/x³`.

**Formalization Note** The sequence is `0`-indexed (`X s` is the paper's `X_{s+1}`), so
`µ̄ₜ = (∑_{s<t} X s)/t`. "`0`-mean `1`-sub-Gaussian" is `HasSubgaussianMGF (X s) 1 P`
(`E[exp(λX)] ≤ exp(λ²/2)` for all `λ`, which forces mean `0`); the variables need not be identically
distributed. `log⁺ a = log(max(a,1))`. -/
theorem lemma_8 {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X P) (h_subG : ∀ s, HasSubgaussianMGF (X s) 1 P)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {x : ℝ} (hx : 0 < x) :
    P.real {ω | ∃ t : ℕ, 0 < t ∧
        (∑ s ∈ Finset.range t, X s ω) / (t : ℝ)
          + Real.sqrt (4 / (t : ℝ) * logPlus (1 / (δ * (t : ℝ) ^ ((3 : ℝ) / 2)))) + x < 0}
      ≤ 39 * δ / x ^ 3 := by sorry

end MaxObjBandit
