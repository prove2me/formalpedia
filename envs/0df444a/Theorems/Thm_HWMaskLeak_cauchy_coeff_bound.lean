-- Prove2me | Theorems.Thm_HWMaskLeak_cauchy_coeff_bound
-- name    : HWMaskLeak.cauchy_coeff_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:29:38.143118+00:00
-- url     : https://prove2.me/theorems/b3c57fd1-3485-4b43-a003-461255dfd8bf
-- title:
--   §2.2 — Cauchy coefficient formula and bound for $\prod_j(1+z\xi_j)$
-- statement:
--   Let $P(z)=\prod_{j=0}^{n-1}(1+z\,\xi_j)$ with $|\xi_j|=1$.
--
--   1. For every $r>0$ and every $w\ge0$,
--   $$
--   [z^w]P(z)=\frac1{2\pi r^w}\int_{-\pi}^{\pi}P(re^{\imath\theta})\exp(-\imath w\theta)\,d\theta.
--   $$
--   2. For $0<w<n$, with $p=w/n$,
--   $$
--   \bigl|[z^w]P(z)\bigr|\le\frac1{2\pi p^w(1-p)^{n-w}}\int_{-\pi}^{\pi}\prod_{j=0}^{n-1}\bigl|(1-p)+p\,\xi_j\exp(\imath\theta)\bigr|\,d\theta.
--   $$
--
--   Part 2 (the substitution $r=p/(1-p)$) turns the coefficient $N\hat B_w(t)$ of eq. (5) into the integral $I$ of Lemma 4.11.
--
--   Differences from the source:
--   - encoding: P(z) = Π_{j=0}^{n−1}(1 + zξ_j) with |ξ_j| = 1 → a polynomial P : ℂ[X] with the hypothesis P = Π_{j : Fin n}(1 + X·C(ξ_j)); interval integrals over [−π, π]; reason: same polynomial and same integrals
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §2.2, Coefficient extraction via Cauchy integration formula, pp.16–17

import Mathlib

namespace HWMaskLeak

open Polynomial

/-- **Coefficient extraction via the Cauchy integral formula** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), §2.2, "Coefficient extraction via
Cauchy integration formula", pp.16–17, unnumbered displays): let `P(z) = Π_{j=0}^{n−1} (1 + z ξ_j)` with
`|ξ_j| = 1`.
1. For every `r > 0`, `[z^w]P(z) = 1/(2π r^w) ∫_{−π}^{π} P(r e^{ıθ}) exp(−ıwθ) dθ`.
2. For `0 < w < n`, with `p = w/n`,
   `|[z^w]P(z)| ⩽ 1/(2π p^w (1 − p)^{n−w}) ∫_{−π}^{π} Π_{j=0}^{n−1} |(1 − p) + p ξ_j exp(ıθ)| dθ`.

**Formalization Note** Part 1 is stated for every `w ∈ ℕ`. The integrals are interval integrals
over `[−π, π]` (complex-valued in part 1, real-valued in part 2) of continuous integrands. -/
theorem cauchy_coeff_bound (n : ℕ) (ξ : Fin n → ℂ) (hξ : ∀ j, ‖ξ j‖ = 1) (P : ℂ[X])
    (hP : P = ∏ j, (1 + X * C (ξ j))) :
    (∀ r : ℝ, 0 < r → ∀ w : ℕ,
      P.coeff w = 1 / ((2 * Real.pi * r ^ w : ℝ) : ℂ) *
        ∫ θ in (-Real.pi)..Real.pi,
          P.eval ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (-((w : ℂ) * (θ : ℂ)) * Complex.I)) ∧
    (∀ w : ℕ, 0 < w → w < n →
      ‖P.coeff w‖ ≤
        1 / (2 * Real.pi * ((w : ℝ) / n) ^ w * (1 - (w : ℝ) / n) ^ (n - w)) *
          ∫ θ in (-Real.pi)..Real.pi,
            ∏ j, ‖((1 - (w : ℝ) / n : ℝ) : ℂ) + (((w : ℝ) / n : ℝ) : ℂ) * ξ j *
              Complex.exp ((θ : ℂ) * Complex.I)‖) := by sorry

end HWMaskLeak
