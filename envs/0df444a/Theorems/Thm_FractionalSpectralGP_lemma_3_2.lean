-- Prove2me | Theorems.Thm_FractionalSpectralGP_lemma_3_2
-- name    : FractionalSpectralGP.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:23:49.422166+00:00
-- url     : https://prove2.me/theorems/f9e85a22-e356-48e3-90bd-533a2b4fe374
-- title:
--   Lemma 3.2 — $\|e_t-e_s\|_{L^2(d\sigma)}\le\sqrt K\,|t-s|$ (corrected: $\sqrt K$ for $K$)
-- statement:
--   Let $\sigma$ be a finite Borel measure on $\mathbb R$ supported in $[-\tfrac12,\tfrac12]$, and let $t,s\in\mathbb R$. Then
--
--   $$
--   \|e_t-e_s\|_{L^2(d\sigma)}\le\sqrt K\,|t-s|,\qquad K=\int_{[-\frac12,\frac12]}u^2\,d\sigma(u).
--   $$
--
--   This Lipschitz estimate for $t\mapsto e_t$ is what makes $X_\sigma$ differentiable in the white noise space (Theorem 6.2).
--
--   Differences from the source:
--   - correction: ‖e_t − e_s‖ ≤ K|t − s| → ‖e_t − e_s‖ ≤ √K |t − s|; reason: false as printed: σ = Lebesgue on [−1/2, 1/2], K = 1/12, t = 0.01, s = 0 gives ‖e_t − e_0‖ ≈ 0.0028867 > K|t| ≈ 0.00083; the paper's proof ends with ‖e_t − e_s‖² ≤ K(t − s)²
--   - reading: σ supported in [−1/2, 1/2] (standing assumption, p.8; K integrates over [−1/2, 1/2]) → hypotheses σ finite and σ(ℝ ∖ [−1/2, 1/2]) = 0; reason: the standing assumption of the section; without it K does not control the norm
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Lemma 3.2, p.8

import Mathlib
import Definitions.Def_FractionalSpectralGP_expL2

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Lemma 3.2 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.8), corrected: for a finite Borel measure `σ` supported in
`[-1/2, 1/2]` and `t, s ∈ ℝ`, `‖e_t − e_s‖_{L²(dσ)} ≤ √K |t − s|` with `K = ∫_{[-1/2,1/2]} u² dσ(u)`.

**Formalization Note.** The page prints `K|t − s|`, which is false (`σ = Leb|_{[-1/2,1/2]}`,
`K = 1/12`, `t = 0.01`, `s = 0`: left side `≈ 0.0028867`, `K|t| ≈ 0.00083`); the paper's own proof
ends with `‖e_t − e_s‖² ≤ K (t − s)²`. The support assumption is the paper's standing one (p.8). -/
theorem lemma_3_2 (σ : Measure ℝ) [IsFiniteMeasure σ]
    (hσ : σ (Set.Icc (-1/2 : ℝ) (1/2))ᶜ = 0) (t s : ℝ) :
    ‖expL2 σ t - expL2 σ s‖ ≤
      Real.sqrt (∫ u in Set.Icc (-1/2 : ℝ) (1/2), u ^ 2 ∂σ) * |t - s| := by sorry

end FractionalSpectralGP
