-- Prove2me | Theorems.Thm_FourExp_expPoly_zero_count
-- name    : FourExp.expPoly_zero_count
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-14T19:01:29.02883+00:00
-- url     : https://prove2.me/theorems/4d055466-a546-41a8-a433-78e09b040998
-- title:
--   Zeros of an exponential polynomial in a disc
-- statement:
--   **Counting zeros of an exponential polynomial.**
--
--   Let $\omega_1, \dots, \omega_l \in \mathbb{C}$ be pairwise distinct, let $q_1, \dots, q_l$ be non-negative integers, and let $b_{j,i}$ ($1 \le j \le l$, $0 \le i < q_j$) be complex numbers, not all zero. Put
--   $$f(z) = \sum_{j=1}^{l} \sum_{i=0}^{q_j - 1} b_{j,i}\, z^{i}\, e^{\omega_j z}, \qquad n = \sum_j q_j, \qquad \Omega = \max_j |\omega_j| .$$
--   Then for every $z_0 \in \mathbb{C}$, every $\rho \ge 0$ and every $\lambda > 0$, the number of zeros of $f$ in the closed disc $|z - z_0| \le \rho$, counted with multiplicity, is less than
--   $$\frac{n}{\lambda} + 2\,\frac{1 + n^{\lambda}}{\lambda \log n}\,(1 + \rho\,\Omega).$$
--
--   **What it is for.** Earlier zero estimates of this kind (Gel'fond, Mahler, Dancs–Turán) depended on a lower bound for $\prod_{i \ne j} |\omega_i - \omega_j|$, which in transcendence proofs forces a Baker-type lower bound for linear forms in logarithms. This one depends only on $n$, $\Omega$ and $\rho$. It is what removes Baker's theorem from the proof of four exponentials in transcendence degree one, and so it feeds `DiazModulus.four_exponentials_trdeg_one`.
--
--   **Formalization.** The count is stated for every finite set $S$ of points in the disc, with each point weighted by `analyticOrderNatAt`. Asking the bound for each $\lambda > 0$ is exactly the paper's minimum over $\lambda$. When $n = 1$ the second term is $0$ under Lean's convention $x/0 = 0$, and the statement is still true because $f = b\,e^{\omega z}$ has no zeros.
-- source:
--   M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §4, Lemme 3, inequality (4.2). Compare R. Tijdeman, Proc. Kon. Nederl. Akad. Wetensch. A 74 (1971), 1–7.

import Mathlib

open Finset

namespace FourExp

theorem expPoly_zero_count
    {l : ℕ} (q : Fin l → ℕ) (ω : Fin l → ℂ) (hω : Function.Injective ω)
    (b : (j : Fin l) → Fin (q j) → ℂ) (hb : ∃ j i, b j i ≠ 0)
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) (lam : ℝ) (hlam : 0 < lam)
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z - z₀‖ ≤ ρ) :
    (∑ z ∈ S, (analyticOrderNatAt
        (fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)) z : ℝ))
      < ((∑ j, q j : ℕ) : ℝ) / lam
        + 2 * (1 + ((∑ j, q j : ℕ) : ℝ) ^ lam) / (lam * Real.log ((∑ j, q j : ℕ) : ℝ))
          * (1 + ρ * ⨆ j, ‖ω j‖) := by
  sorry

end FourExp
