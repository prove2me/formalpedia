-- Prove2me | Theorems.Thm_LogLogJam_lemma_5_5
-- name    : LogLogJam.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:14.600605+00:00
-- url     : https://prove2.me/theorems/42a10db2-c407-480f-b07b-8bf79d78d4a6
-- title:
--   Lemma 5.5 — $\int\max_\theta q_\theta(H)\,dH\le1+\pi\sqrt{\bar J}$
-- statement:
--   Let $(X,\mu)$ be a measure space (the histories) and, for each $\theta\in\mathbb R$, let $q_\theta$ be a probability density on $X$, positive, $\pi$-periodic and continuously differentiable in $\theta$, and measurable in $x$. Let $J(\theta)$ be the Fisher information of $(q_\theta)$ and $\bar J=\frac1\pi\int_0^\pi J(\theta)\,d\theta$. Then
--
--   $$
--   \int_X\max_{\theta\in\mathbb T}q_\theta(x)\,d\mu(x)\le1+\pi\sqrt{\bar J}.
--   $$
--
--   Through Hölder's inequality this converts a bound on the average Fisher information into a bound on the success probability (Lemma 5.4).
--
--   Differences from the source:
--
--   - reading: “any joint probability density $q(\theta,H_t)$ over $\mathbb T\times\mathcal H$” → a family of conditional densities $q_\theta$ on a measure space $(X,\mu)$ with $\int q_\theta\,d\mu=1$, positive, $C^1$ and $\pi$-periodic in $\theta$, measurable in $x$; reason: the joint density under the uniform prior is $q_\theta(H)/\pi$; the regularity is what a density with a Fisher information carries implicitly (the proof differentiates in $\theta$ and integrates the derivative)
--   - encoding: $\max_{\theta\in\mathbb T}$ → $\sup_{\theta\in\mathbb R}$; reason: equal by $\pi$-periodicity and continuity
--   - encoding: probabilities, expectations and Fisher informations as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative functions); reason: every quantity is a nonnegative integral; the extended value avoids junk zeros for non-integrable integrands and agrees with the real value when finite
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Lemma 5.5, p.24 (PDF p.27)

import Mathlib
import Definitions.Def_LogLogJam_fisherInfo

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

/-- **Lemma 5.5** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Lemma 5.5, p.24): "For any joint probability density q(θ, H_t) over the set
𝕋 × ℋ, we have ∫ max_{θ∈𝕋} q_θ(H_t) dH_t ≤ 1 + π √J̄_t."

Here `q_θ` is a probability density on a measure space `(X, μ)` of histories for each `θ`,
`π`-periodic in `θ`, `J(θ)` its Fisher information and `J̄ = (1/π) ∫_0^π J(θ) dθ`.

**Formalization Note** The regularity implicit in "probability density" with a Fisher information is
stated: `q > 0`, `q` is `C¹` in `θ` and measurable in `x`. The maximum over `𝕋` is the supremum over
`θ ∈ ℝ` (equal by periodicity). Values in `[0, ∞]`. -/
theorem lemma_5_5 {X : Type*} [MeasurableSpace X] (μ : Measure X) (q : ℝ → X → ℝ)
    (hpos : ∀ θ x, 0 < q θ x) (hper : ∀ θ x, q (θ + Real.pi) x = q θ x)
    (hC1 : ∀ x, ContDiff ℝ 1 (fun θ => q θ x)) (hmeas : ∀ θ, Measurable (q θ))
    (hnorm : ∀ θ, ∫⁻ x, ENNReal.ofReal (q θ x) ∂μ = 1) :
    ∫⁻ x, ⨆ θ, ENNReal.ofReal (q θ x) ∂μ ≤
      1 + ENNReal.ofReal Real.pi *
        (ENNReal.ofReal (1 / Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi, fisherInfo μ q θ) ^ (1 / 2 : ℝ) := by sorry

end LogLogJam
