-- Prove2me | Theorems.Thm_MasulloGRH_weighted_L2_to_L1_positiveHaar
-- name    : MasulloGRH.weighted_L2_to_L1_positiveHaar
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-21T00:07:29.706016+00:00
-- url     : https://prove2.me/theorems/378025df-2285-4390-b8f0-bf091d7c5a63
-- title:
--   Weighted L2 embeds continuously into L1 for positive-real Haar measure
-- statement:
--   Let $s>1$ and let $d\mu(t)=dt/t$ on $(0,\infty)$. There is a finite constant $C_s>0$ such that, for every complex-valued function $f$ whose weighted $L^2$ norm is finite,
--
--   $$\left\|(1+(\log t)^2)^{s/4}f(t)\right\|_{L^2(\mu)}<\infty,$$
--
--   one has $f\in L^1(\mu)$ and
--
--   $$\|f\|_{L^1(\mu)}\le C_s\left\|(1+(\log t)^2)^{s/4}f(t)\right\|_{L^2(\mu)}.$$
--
--   This is the positive-real coordinate form of the weighted Cauchy–Schwarz argument in Proposition 9.1.2.6. It establishes both integrability and a uniform norm estimate, rather than relying on a totalized integral for a potentially nonintegrable function.
--
--   Formalization Note: $\mu$ is defined as the pushforward of Lebesgue measure on $\mathbb R$ under $x\mapsto e^x$. Functions are represented on $\mathbb R$, but this measure is supported on $(0,\infty)$. The constant and norms are encoded as extended nonnegative reals, with $0<C_s<\infty$ explicit. The general compact-fiber modulated-group reduction is not part of this statement.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, pp. 402–403, Proposition 9.1.2.6 and equation (9.1.2.17), with Lemma 9.1.2.4 supplying integrability of the reciprocal weight, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. The Lean theorem is the positive-real multiplicative-group specialization of the weighted Cauchy–Schwarz estimate.

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal

theorem MasulloGRH.weighted_L2_to_L1_positiveHaar (s : ℝ) (hs : 1 < s) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧ ∀ f : ℝ → ℂ,
      MemLp (fun t => ((1 + (Real.log t) ^ 2) ^ (s / 4) : ℝ) • f t)
        2 (Measure.map Real.exp volume) →
      Integrable f (Measure.map Real.exp volume) ∧
      eLpNorm f 1 (Measure.map Real.exp volume) ≤
        C * eLpNorm (fun t => ((1 + (Real.log t) ^ 2) ^ (s / 4) : ℝ) • f t)
          2 (Measure.map Real.exp volume) := by sorry
