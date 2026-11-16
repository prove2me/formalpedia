-- Prove2me | Theorems.Thm_GuthMaynard_van_der_corput_b_process
-- name    : GuthMaynard.van_der_corput_b_process
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T19:01:48.687126+00:00
-- url     : https://prove2.me/theorems/389ffa3b-ab9c-48d2-810c-6e59f3a59820
-- title:
--   Van der Corput's B-process — an exponential sum is a dual sum over stationary points, up to explicit errors
-- statement:
--   Let $R \ge 1$ be real. There are a complex number $\kappa$ and a constant $C > 0$, depending only on $R$, with the following property. Let $a < b$ be natural numbers and $\lambda_2, \lambda_3 > 0$. Let $f$ be a real function that is three times differentiable on $[a,b]$, with
--   $$\lambda_2 \le f''(x) \le R\lambda_2, \qquad |f'''(x)| \le R\lambda_3 \qquad (a \le x \le b).$$
--   For every integer $\nu$ with $f'(a) < \nu \le f'(b)$ let $x_\nu \in [a,b]$ be a point with $f'(x_\nu) = \nu$. Then
--   $$\Big|\sum_{a<n\le b} e^{2\pi i f(n)} - \kappa\sum_{f'(a) < \nu \le f'(b)} f''(x_\nu)^{-1/2}\, e^{2\pi i (f(x_\nu) - \nu x_\nu)}\Big| \le C\Big(\lambda_2^{-1/2} + \log\big(2 + (b-a)\lambda_2\big) + (b-a)\,\lambda_2^{1/5}\lambda_3^{1/5}\Big).$$
--
--   This is Theorem 4.9 of E. C. Titchmarsh, *The theory of the Riemann zeta-function* (2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986), Chapter IV, in the case of a positive second derivative. It is the B-process of van der Corput's method.
--
--   **Formalization note.**
--   - The constant $\kappa$ is asserted to exist and is not identified. In the classical statement $\kappa = e^{\pi i/4}$, which this statement does not assert. The same $\kappa$ serves every $f$, $a$, $b$, $\lambda_2$, $\lambda_3$ for the given $R$.
--   - The function and its derivatives are given as four real functions $f, f_1, f_2, f_3$ on $\mathbb{R}$, each the derivative of the one before at every point of $[a,b]$ (two-sided derivatives, also at the endpoints).
--   - The stationary points are given as a function $X$ from the integers to the reals, with $X(\nu) \in [a,b]$ and $f_1(X(\nu)) = \nu$ required for $f_1(a) < \nu \le f_1(b)$; its other values play no role.
--   - The dual sum is over the integers $\nu$ with $\lfloor f_1(a)\rfloor < \nu \le \lfloor f_1(b)\rfloor$, which are exactly the integers with $f_1(a) < \nu \le f_1(b)$.
--   - Only $f'' > 0$ is covered. For $f'' < 0$, apply the statement to $-f$ and take complex conjugates.
-- source:
--   Titchmarsh, E. C., The theory of the Riemann zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press (1986) (a book; no DOI), Chapter IV, Theorem 4.9 (van der Corput's B-process), for a positive second derivative, a step of a proof of μ(1/2) ≤ 27/164

import Mathlib

namespace GuthMaynard

theorem van_der_corput_b_process (R : ℝ) (hR : 1 ≤ R) :
    ∃ κ : ℂ, ∃ C : ℝ, 0 < C ∧ ∀ (f f1 f2 f3 : ℝ → ℝ) (X : ℤ → ℝ) (a b : ℕ) (lam2 lam3 : ℝ),
      a < b → 0 < lam2 → 0 < lam3 →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f1 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f1 (f2 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f2 (f3 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, lam2 ≤ f2 x ∧ f2 x ≤ R * lam2) →
      (∀ x ∈ Set.Icc (a : ℝ) b, |f3 x| ≤ R * lam3) →
      (∀ ν : ℤ, f1 a < ν → (ν : ℝ) ≤ f1 b → X ν ∈ Set.Icc (a : ℝ) b ∧ f1 (X ν) = ν) →
      ‖∑ n ∈ Finset.Ioc a b, Complex.exp (((2 * Real.pi * f n : ℝ) : ℂ) * Complex.I) -
          κ * ∑ ν ∈ Finset.Ioc ⌊f1 a⌋ ⌊f1 b⌋,
            ((f2 (X ν) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              Complex.exp (((2 * Real.pi * (f (X ν) - (ν : ℝ) * X ν) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (lam2 ^ (-(1 / 2 : ℝ)) + Real.log (2 + ((b : ℝ) - a) * lam2) +
          ((b : ℝ) - a) * lam2 ^ (1 / 5 : ℝ) * lam3 ^ (1 / 5 : ℝ)) := by
  sorry

end GuthMaynard
