-- Prove2me | Theorems.Thm_FoundationsRL_TailBounds_lemma_39
-- name    : FoundationsRL.TailBounds.lemma_39
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:34.109842+00:00
-- url     : https://prove2.me/theorems/c388cdf7-3ba4-47a8-aab6-9b2a7ac7e357
-- title:
--   Lemma 39 — Pinsker-type mean bound for sub-Gaussian laws
-- statement:
--   Let $P$ and $Q$ be probability distributions on $\mathbb R$, the laws of $X\sim P$ and $Y\sim Q$, and suppose both are $\sigma^2$-sub-Gaussian: $\mathbb E\,e^{\lambda(X-\mathbb E X)}\le e^{\sigma^2\lambda^2/2}$ for all $\lambda\in\mathbb R$, and likewise for $Y$. Then
--   $$
--   \big|\mathbb E_P[X]-\mathbb E_Q[Y]\big|\le\sqrt{2\sigma^2\cdot D_{\mathrm{KL}}(P\,\|\,Q)}.
--   $$
--
--   Closeness in KL divergence therefore forces closeness of means at the Gaussian rate. This change-of-measure bound converts information-theoretic distances between models into differences of mean rewards in lower-bound arguments.
--
--   **Formalization Note** $X$ and $Y$ are the identity of $\mathbb R$ under $P$ and $Q$. Sub-Gaussianity is the published definition with parameter $\sigma$ (variance proxy $\sigma^2$), which includes integrability of the variable and of its exponential moments. $D_{\mathrm{KL}}$ is Mathlib's `klDiv`, valued in $[0,\infty]$; it is assumed finite, and the bound is stated between real numbers.
--
--   Differences from the source:
--   - encoding: random variables X ∼ P and Y ∼ Q → laws P, Q on ℝ and the identity map; reason: E_P[X] and D_KL(P ∥ Q) depend only on the laws; same instances
--   - encoding: σ²-sub-Gaussian (Definition 2, p. 10) → IsSubGaussian with parameter σ, including integrability of x and of every e^{λ(x − E x)}; reason: Definition 2 presupposes these expectations exist; Bochner integrals would otherwise be the junk 0
--   - encoding: D_KL(P ∥ Q) ∈ [0, ∞] → klDiv P Q ≠ ∞ assumed, right side in ℝ via toReal; reason: when D_KL = ∞ the right side is +∞ (or the undefined 0·∞ at σ = 0) and the claim says nothing
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 39, p. 158

import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubGaussian
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace FoundationsRL.TailBounds

/-- **Lemma 39** (Pinsker for sub-Gaussian random variables). Suppose that `X ∼ P` and `Y ∼ Q` are
both `σ²`-sub-Gaussian. Then `|E_P[X] − E_Q[Y]| ≤ √(2σ² · D_KL(P ∥ Q))`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Lemma 39, p. 158.

**Formalization Note.** `P` and `Q` are the laws on `ℝ` of `X` and `Y`, so `X` and `Y` are the
identity of `ℝ` under `P` and `Q`. "`σ²`-sub-Gaussian" is Definition 2 (p. 10) with variance proxy
`σ²`, the published `HighDimStat.TailBounds.IsSubGaussian` with parameter `σ` (it carries
integrability of `X` and of its exponential moments). `D_KL` is Mathlib's `klDiv`, valued in
`[0, ∞]`; it is assumed finite, the case `D_KL = ∞` (right side `+∞`) being trivial, so the
statement is in `ℝ` with `.toReal`. -/
theorem lemma_39 (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (σ : ℝ)
    (hP : HighDimStat.TailBounds.IsSubGaussian (fun x : ℝ => x) P σ)
    (hQ : HighDimStat.TailBounds.IsSubGaussian (fun x : ℝ => x) Q σ)
    (hKL : klDiv P Q ≠ ∞) :
    |∫ x, x ∂P - ∫ x, x ∂Q| ≤ Real.sqrt (2 * σ ^ 2 * (klDiv P Q).toReal) := by sorry

end FoundationsRL.TailBounds
