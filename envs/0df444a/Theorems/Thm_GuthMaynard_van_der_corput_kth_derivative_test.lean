-- Prove2me | Theorems.Thm_GuthMaynard_van_der_corput_kth_derivative_test
-- name    : GuthMaynard.van_der_corput_kth_derivative_test
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T19:01:50.106755+00:00
-- url     : https://prove2.me/theorems/f2854069-7273-4f9b-ad9d-a4c5372c8494
-- title:
--   Van der Corput's k-th derivative test for exponential sums
-- statement:
--   Let $k \ge 2$ be an integer and $R \ge 1$ a real number, and put $K = 2^{k-1}$. There is a constant $C > 0$, depending only on $k$ and $R$, with the following property. Let $a < b$ be natural numbers, and let $f$ be a real function that is $k$ times differentiable on $[a, b]$, such that for some $\lambda > 0$ either $\lambda \le f^{(k)}(x) \le R\lambda$ for all $x \in [a,b]$, or $\lambda \le -f^{(k)}(x) \le R\lambda$ for all $x \in [a,b]$. Then
--   $$\Big|\sum_{a < n \le b} e^{2\pi i f(n)}\Big| \le C\Big((b-a)\,\lambda^{1/(2K-2)} + (b-a)^{1-2/K}\,\lambda^{-1/(2K-2)}\Big).$$
--
--   This is Theorem 5.13 of E. C. Titchmarsh, *The theory of the Riemann zeta-function* (2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986), Chapter V. For $k = 2$ it is the second-derivative test (`ExponentialSums.vdC_second_derivative` is a form of it), with exponents $1/2$ and $-1/2$; for $k = 4$ the exponents of $\lambda$ are $\pm 1/14$, and for $k = 5$ they are $\pm 1/30$.
--
--   **Formalization note.**
--   - The function and its derivatives are given as a sequence $F_0 = f, F_1, \dots, F_k$ of real functions on $\mathbb{R}$ with $F_{j+1}(x)$ the derivative of $F_j$ at every $x \in [a,b]$, for $j < k$ (two-sided derivatives, also at the endpoints). The functions $F_j$ with $j > k$ play no role. No continuity of $F_k$ is assumed.
--   - The sign of the $k$-th derivative is a number $\sigma \in \{1, -1\}$, and the hypothesis is $\lambda \le \sigma F_k(x) \le R\lambda$.
--   - The dependence of the constant on the ratio $R$ is not made explicit: the constant is chosen after $k$ and $R$ and before everything else.
--   - The endpoints $a, b$ are natural numbers, and the sum is over the integers $a < n \le b$.
-- source:
--   Titchmarsh, E. C., The theory of the Riemann zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press (1986) (a book; no DOI), Chapter V, Theorem 5.13 (van der Corput's k-th derivative test), with the constant depending on k and on the ratio of the bounds for the k-th derivative, a step of a proof of μ(1/2) ≤ 27/164

import Mathlib

namespace GuthMaynard

theorem van_der_corput_kth_derivative_test (k : ℕ) (hk : 2 ≤ k) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℕ → ℝ → ℝ) (a b : ℕ) (lam σ : ℝ), a < b → 0 < lam →
      (σ = 1 ∨ σ = -1) →
      (∀ j < k, ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt (F j) (F (j + 1) x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, lam ≤ σ * F k x ∧ σ * F k x ≤ R * lam) →
      ‖∑ n ∈ Finset.Ioc a b, Complex.exp (((2 * Real.pi * F 0 n : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (((b : ℝ) - a) * lam ^ (1 / (2 * (2 : ℝ) ^ (k - 1) - 2)) +
          ((b : ℝ) - a) ^ (1 - 2 / (2 : ℝ) ^ (k - 1)) *
            lam ^ (-(1 / (2 * (2 : ℝ) ^ (k - 1) - 2)))) := by
  sorry

end GuthMaynard
