-- Prove2me | Theorems.Thm_FourExp_expPoly_zero_count_scaled
-- name    : FourExp.expPoly_zero_count_scaled
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-15T03:45:34.420118+00:00
-- url     : https://prove2.me/theorems/0fdacfda-2630-482e-8cf1-f159d6ba6be7
-- title:
--   Zeros of an exponential polynomial: the rescaled Cauchy–interpolation inequality
-- statement:
--   **The analytic core of the zero count, before any choice of radius.**
--
--   Take $f(z) = \sum_j \sum_{i < q_j} b_{j,i} z^i e^{\omega_j z}$ with distinct $\omega_j$ and not all $b_{j,i}$ zero. Put $n = \sum_j q_j$ and $\Omega = \max_j|\omega_j| > 0$. Let $\sigma$ be the number of zeros of $f$, with multiplicity, at the points of a finite set $S$ inside the disc $|z - z_0| \le \rho$, and put $x = \rho\,\Omega$. Then for every $R > x + 1$,
--   $$\sigma \,\log\frac{R - x}{x + 1} \;\le\; \log\Bigl(n!\, 2^{n+1} \frac{R}{R-1}\Bigr) + 2R .$$
--
--   **Proof idea** (Waldschmidt 1971, §4). Two estimates bound $\max_{s<n} |g^{(s)}(0)|$ against $\max_{|u| = R}|g(u)|$ in opposite directions:
--   - **From above.** A Cauchy estimate that uses the $\sigma$ zeros in $|z| \le r$ gives $|g^{(s)}(0)| \le s!\, \frac{R}{R-1} \bigl(\frac{r+1}{R-r}\bigr)^{\sigma} \max_{|u|=R}|g|$. This is (4.3).
--   - **From below.** Solving the confluent Vandermonde system for the coefficients and bounding the interpolation polynomial gives $\max_{s < n}|g^{(s)}(0)| \ge [n(W+1)^{n+1} e^{R(W+1)}]^{-1}\max_{|u|=R}|g|$, where $W$ bounds the frequencies. These are (4.5)–(4.13).
--
--   Apply both to $g(z) = f(z_0 + z/\Omega)$, whose frequencies have modulus at most $1$ and whose zeros from $S$ lie in $|z| \le \rho\Omega$.
--
--   **What it is for.** Together with `FourExp.zero_count_arith` it gives the zero count `FourExp.expPoly_zero_count` when $n \ge 2$ and $\Omega > 0$.
-- source:
--   M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §4, inequality (4.14) and the rescaling that follows it.

import Mathlib

open Finset

namespace FourExp

theorem expPoly_zero_count_scaled
    {l : ℕ} (q : Fin l → ℕ) (ω : Fin l → ℂ) (hω : Function.Injective ω)
    (b : (j : Fin l) → Fin (q j) → ℂ) (hb : ∃ j i, b j i ≠ 0)
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z - z₀‖ ≤ ρ)
    (hΩ : 0 < ⨆ j, ‖ω j‖) :
    ∀ R : ℝ, ρ * (⨆ j, ‖ω j‖) + 1 < R →
      (∑ z ∈ S, (analyticOrderNatAt (fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)) z : ℝ))
          * Real.log ((R - ρ * (⨆ j, ‖ω j‖)) / (ρ * (⨆ j, ‖ω j‖) + 1))
        ≤ Real.log (((∑ j, q j).factorial : ℝ) * 2 ^ ((∑ j, q j) + 1) * R / (R - 1)) + 2 * R := by
  sorry

end FourExp
