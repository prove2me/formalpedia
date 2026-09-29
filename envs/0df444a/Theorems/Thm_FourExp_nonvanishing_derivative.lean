-- Prove2me | Theorems.Thm_FourExp_nonvanishing_derivative
-- name    : FourExp.nonvanishing_derivative
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-14T19:24:48.322202+00:00
-- url     : https://prove2.me/theorems/6b3e7ded-6c39-4625-b4ac-f87189de2224
-- title:
--   A derivative of an exponential polynomial is non-zero somewhere on a lattice
-- statement:
--   **Some derivative of an exponential polynomial survives on a lattice.**
--
--   Let $x_1, x_2$ be linearly independent over $\mathbb{Q}$, and likewise $y_1, y_2$. For complex coefficients $c(i, j, k)$ ($0 \le i < S$, $0 \le j, k < T$), not all zero, put
--   $$G(z) = \sum_{i < S} \sum_{j, k < T} c(i,j,k)\, z^{i}\, e^{(j x_1 + k x_2) z} .$$
--   Let $R_1, R_2, S'$ be positive integers and $\lambda > 0$, with $n = S T^2$, such that
--   $$\frac{n}{\lambda} + 2\,\frac{1 + n^{\lambda}}{\lambda \log n}\,\Bigl(1 + (R_1|y_1| + R_2|y_2|)\,T\,(|x_1| + |x_2|)\Bigr) \le R_1 R_2 S' .$$
--   Then there are $a < R_1$, $b < R_2$ and $s < S'$ with $G^{(s)}(a y_1 + b y_2) \ne 0$.
--
--   **Proof idea.** Otherwise each of the $R_1 R_2$ points $a y_1 + b y_2$ is a zero of order at least $S'$. They are distinct because $y_1, y_2$ are $\mathbb{Q}$-independent, and they lie in the disc of radius $R_1|y_1| + R_2|y_2|$. The frequencies $j x_1 + k x_2$ are distinct because $x_1, x_2$ are $\mathbb{Q}$-independent, and have modulus at most $T(|x_1| + |x_2|)$. So `FourExp.expPoly_zero_count` bounds the number of zeros strictly below $R_1 R_2 S'$. A contradiction, provided $G \not\equiv 0$.
--
--   **What it is for.** This is step (3), Lemma 6, of Waldschmidt's 1973 proof of four exponentials in transcendence degree one, with the zero estimate of his 1971 paper in place of Gel'fond's. That swap removes the need for a Baker-type lower bound on $|n_1 + n_2 x_2/x_1|$. It feeds `FourExp.small_polynomials_of_counterexample`.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Lemma 6; with M. Waldschmidt, Bull. Soc. Math. France 99 (1971), 285–304, §4, Lemma 3 in place of Gel'fond's zero lemma.

import Mathlib

namespace FourExp

theorem nonvanishing_derivative
    (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂]) (hy : LinearIndependent ℚ ![y₁, y₂])
    (S T R₁ R₂ S' : ℕ) (c : Fin S → Fin T → Fin T → ℂ) (hc : ∃ i j k, c i j k ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (hcount : (((S * T * T : ℕ) : ℝ) / lam
              + 2 * (1 + ((S * T * T : ℕ) : ℝ) ^ lam) / (lam * Real.log ((S * T * T : ℕ) : ℝ))
                * (1 + ((R₁ : ℝ) * ‖y₁‖ + (R₂ : ℝ) * ‖y₂‖) * ((T : ℝ) * (‖x₁‖ + ‖x₂‖)))
            ≤ ((R₁ * R₂ * S' : ℕ) : ℝ))) :
    ∃ a b s : ℕ, a < R₁ ∧ b < R₂ ∧ s < S' ∧
      iteratedDeriv s (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              c i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
        ((a : ℂ) * y₁ + (b : ℂ) * y₂) ≠ 0 := by
  sorry

end FourExp
