-- Prove2me | Theorems.Thm_MarkdownReadjust_lemma_EC_5
-- name    : MarkdownReadjust.lemma_EC_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:11:54.731996+00:00
-- url     : https://prove2.me/theorems/1bde005e-191d-4ead-a17c-8b739cb7500c
-- title:
--   Lemma EC.5 — Poisson tail with a bounded random rate
-- statement:
--   Let $\lambda>0$ and let $\Lambda\in(0,\lambda]$ be a random variable. Let $X$ be a random variable that, conditionally on $\Lambda$, is Poisson with parameter $\Lambda$. Then for every $\epsilon>0$,
--
--   $$
--   \mathbb P(X-\Lambda\ge\epsilon)\le\exp\Big(-0.1\,\epsilon\,\min\Big\{\frac\epsilon\lambda,1\Big\}\Big).
--   $$
--
--   This concentration bound is what makes the bad event $\mathcal G^c$ unlikely (Lemma EC.4).
--
--   Differences from the source:
--   - encoding: random variables Λ ∈ (0,λ] and X with X | Λ ~ Poisson(Λ) → an arbitrary probability measure μ on ℝ with μ((0,λ]ᶜ) = 0 and P(X − Λ ≥ ε) = ∫ Po(Λ){n : n − Λ ≥ ε} dμ(Λ); reason: the joint law of (Λ, X) is this mixture; same instances
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Lemma EC.5, p.ec24

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MarkdownReadjust

/-- **Lemma EC.5, p.ec24** (Chen–Jasin, SSRN 3740871). Let `Λ ∈ (0, λ]` be a random variable
and let `X`, conditionally on `Λ`, be Poisson with parameter `Λ`. Then for every `ε > 0`,
`P(X − Λ ≥ ε) ≤ exp(−0.1 ε min{ε/λ, 1})`.

**Formalization Note.** The law of `Λ` is an arbitrary probability measure `μ` on `ℝ`
concentrated on `(0, λ]`, and `P(X − Λ ≥ ε) = ∫ Po(Λ){n : n − Λ ≥ ε} dμ(Λ)` (the mixture). -/
theorem lemma_EC_5 (lam : ℝ) (hlam : 0 < lam) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Ioc 0 lam)ᶜ = 0) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ Λ, poissonMeasure Λ.toNNReal {n : ℕ | ε ≤ (n : ℝ) - Λ} ∂μ
      ≤ ENNReal.ofReal (Real.exp (-0.1 * ε * min (ε / lam) 1)) := by sorry

end MarkdownReadjust
