-- Prove2me | Theorems.Thm_LogLogJam_lemma_5_11
-- name    : LogLogJam.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:04.302482+00:00
-- url     : https://prove2.me/theorems/f3c1eb7c-5a0b-4e74-b03e-6a7120a3454f
-- title:
--   Lemma 5.11 — $\|p\|_{L^\infty(\mathbb T)}\le1/\pi+\sqrt{F(p)}$
-- statement:
--   Let $p$ be a positive, continuously differentiable probability density on $\mathbb T=\mathbb R/\pi\mathbb Z$. Then for every $\theta$,
--
--   $$
--   p(\theta)\le\frac1\pi+\sqrt{F(p)},\qquad F(p)=\mathbb E_{\theta\sim p}\big[(\partial_\theta\log p(\theta))^2\big],
--   $$
--
--   so $\|p\|_{L^\infty(\mathbb T)}\le1/\pi+\sqrt{F(p)}$. A posterior with little Fisher information cannot be concentrated.
--
--   Differences from the source:
--
--   - generalization: positive smooth density → positive $C^1$ density; reason: every smooth density is $C^1$, and the proof uses only the fundamental theorem of calculus for $p$
--   - encoding: $\max_\theta p(\theta)\le\dots$ → $p(\theta)\le\dots$ for every $\theta$; reason: equivalent
--   - encoding: $\theta\in\mathbb T=\mathbb R/\pi\mathbb Z$, uniform law and integrals on $\mathbb T$ → $\theta\in\mathbb R$ with $\pi$-periodic objects; uniform law and integrals over $[0,\pi)$; reason: $V_{\lambda,\theta}$ is $\pi$-periodic, so $[0,\pi)$ is one period; same instances
--   - encoding: probabilities, expectations and Fisher informations as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative functions); reason: every quantity is a nonnegative integral; the extended value avoids junk zeros for non-integrable integrands and agrees with the real value when finite
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Lemma 5.11, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_LogLogJam_fisherInfo

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

/-- **Lemma 5.11** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Lemma 5.11, p.27): "For every positive smooth probability density p on
𝕋, ‖p‖_{L∞(𝕋)} := max_{θ∈𝕋} p(θ) is upper bounded by ‖p‖_{L∞(𝕋)} ≤ 1/π + √F(p), where
F(p) = E_{θ∼p}[(∂_θ log p(θ))²]."

**Formalization Note** A density on `𝕋 = ℝ/πℤ` is a `π`-periodic function on `ℝ` integrating to `1`
over `[0, π)`; "smooth" is weakened to `C¹`. The bound is stated at every `θ`. -/
theorem lemma_5_11 (p : ℝ → ℝ) (hpos : ∀ θ, 0 < p θ) (hper : ∀ θ, p (θ + Real.pi) = p θ)
    (hC1 : ContDiff ℝ 1 p) (hnorm : ∫ θ in Set.Ico 0 Real.pi, p θ = 1) (θ : ℝ) :
    ENNReal.ofReal (p θ) ≤ ENNReal.ofReal (1 / Real.pi) + (circFisher p) ^ (1 / 2 : ℝ) := by sorry

end LogLogJam
