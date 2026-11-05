-- Prove2me | Theorems.Thm_FourierRestriction_restriction_zero_of_restriction_of_fourier_decay
-- name    : FourierRestriction.restriction_zero_of_restriction_of_fourier_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T14:40:31.976018+00:00
-- url     : https://prove2.me/theorems/d79e3b80-57e3-4a5f-b238-34c838cf07d5
-- title:
--   ε-removal for measures with Fourier decay — a local restriction estimate R_μ(p, α) gives the global estimate R_μ(q, 0)
-- statement:
--   Let $n \ge 2$ and let $\mu$ be a finite Borel measure on $\mathbb{R}^n$ carried by some closed ball, whose Fourier transform decays like a power: there are $C$ and $c > 0$ with
--   $$\Bigl|\int e^{-2\pi i \langle \xi, x\rangle}\, d\mu(\xi)\Bigr| \le C (1 + |x|)^{-c} \quad \text{for all } x \in \mathbb{R}^n.$$
--   For $p \ge 1$ and real $\alpha$, write $R_\mu(p, \alpha)$ for the localized restriction estimate: there is $C$ such that $\|\hat f\|_{L^p(\mu)} \le C R^\alpha \|f\|_{L^p(\mathbb{R}^n)}$ for every $R \ge 1$ and every Schwartz function $f$ supported in the closed ball $\overline{B}(0, R)$.
--
--   Then there are constants $\kappa$ and $\alpha_0 > 0$, depending on $n$ and $\mu$, such that whenever $1 < p < 2$ and $0 < \alpha < \alpha_0$, the estimate $R_\mu(p, \alpha)$ implies $R_\mu(q, 0)$ for every $q \ge 1$ with
--   $$\frac1q > \frac1p + \frac{\kappa}{\log(1/\alpha)}.$$
--   No Frostman (dimension) bound on $\mu$ is assumed: power decay of $\hat\mu$ and bounded support are the only hypotheses.
--
--   This is the argument of Theorem 1.2 of T. Tao, *The Bochner–Riesz conjecture implies the restriction conjecture*, Duke Math. J. 96 (1999) 363–375 (preprint p. 2), "If $1 < p < 2$ and $0 < \alpha \ll 1$, then $R(p,\alpha) \implies R(q,0)$ whenever $\frac1q > \frac1p + \frac{C}{\log\frac1\alpha}$", there stated for surface measure on the sphere, here stated for a general measure. The Tao 1999 mission's proof of Theorem 4.9 needed it for the push-forward measures $\mu_q$ of `TaoBR.linearizedMeasure_fourier_decay_of_oscillatoryOp_le`.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 2, Theorem 1.2 (the epsilon-removal argument), stated for any finite measure on R^n with bounded support and power Fourier decay instead of surface measure on the sphere

import Mathlib

open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace

namespace FourierRestriction

theorem restriction_zero_of_restriction_of_fourier_decay (n : ℕ) (hn : 2 ≤ n)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure μ]
    (hsupp : ∃ r : ℝ, μ (closedBall 0 r)ᶜ = 0)
    (hdecay : ∃ C c : ℝ, 0 < c ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      ‖∫ ξ, (𝐞 (-⟪ξ, x⟫) : ℂ) ∂μ‖ ≤ C * (1 + ‖x‖) ^ (-c)) :
    ∃ κ α₀ : ℝ, 0 < α₀ ∧ ∀ p : ℝ, 1 < p → p < 2 → ∀ α : ℝ, 0 < α → α < α₀ →
      (∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        tsupport f ⊆ closedBall 0 R →
          eLpNorm (𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ)) (ENNReal.ofReal p) μ ≤
            C * ENNReal.ofReal (R ^ α) * eLpNorm f (ENNReal.ofReal p) volume) →
      ∀ q : ℝ, 1 ≤ q → 1 / p + κ / Real.log (1 / α) < 1 / q →
        ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          tsupport f ⊆ closedBall 0 R →
            eLpNorm (𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ)) (ENNReal.ofReal q) μ ≤
              C * eLpNorm f (ENNReal.ofReal q) volume := by
  sorry

end FourierRestriction
