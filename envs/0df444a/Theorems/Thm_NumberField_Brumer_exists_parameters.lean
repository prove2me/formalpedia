-- Prove2me | Theorems.Thm_NumberField_Brumer_exists_parameters
-- name    : NumberField.Brumer.exists_parameters
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T09:28:19.97701+00:00
-- url     : https://prove2.me/theorems/bc720443-29dd-45fb-b6af-0153e851160d
-- title:
--   Brumer's theorem: existence of the parameters of Baker's method
-- statement:
--   Let $n, d \ge 1$ and $q \ge 0$ be integers and let $C_1, C_3 \ge 1$ and $0 \le \rho < 1$ be real numbers. The statement asserts that there are integers $N \ge 1$ and $J \ge 0$ and sequences of natural numbers $S_0 \ge S_1 \ge \dots$ and $R_0, R_1, \dots$ such that
--
--   1. $2\, d\, (S_0 + 1)^{n-1} R_0 \le N^n$,
--   2. $N^n \le R_J$, and
--   3. for each $j < J$, with $B = N^n C_1^{\,N R_0 + S_0} N^{S_0}$,
--   $$\rho^{\,R_j (S_j - S_{j+1})} \cdot \Bigl( N^n \, B\, C_3^{\,q N R_{j+1} + S_{j+1}} \, N^{S_{j+1}} \Bigr)^{d} < 1 .$$
--
--   **Meaning.** Condition 1 is the count condition of Siegel's lemma for an auxiliary function with $N^n$ coefficients that vanishes to order $S_0$ at $R_0$ points; $B$ is the bound for its coefficients. Condition 3 is the numerical condition of the extrapolation step from $(S_j, R_j)$ to $(S_{j+1}, R_{j+1})$, where $\rho = \|p\|_w$. Condition 2 says that after $J$ steps there are enough points for the Vandermonde argument.
--
--   **Proof idea.** Take a large parameter $h$, $N \approx h^{2 - 1/(2n)}$, $S_j \approx h^2/2^j$, $R_j \approx h^{1 + j/(4n)}$ and $J = 8n^2$. Then $R_j (S_j - S_{j+1}) \approx h^{3 + j/(4n)}/2^{j+1}$, while the logarithm of the second factor in condition 3 is of order $h^{3 + j/(4n) - 1/(4n)}$. Since $J$ does not depend on $h$, condition 3 holds for large $h$. Conditions 1 and 2 are comparisons of powers of $h$.
--
--   **Use.** With these parameters, `NumberField.Brumer.exists_int_coeffs_vanishing` and $J$ applications of `NumberField.Brumer.extrapolation_step` give `NumberField.Brumer.exists_auxiliary_polynomial`.
--
--   **Formalization Note.** The statement is pure real arithmetic (`import Mathlib`). $S$ and $R$ are functions `ℕ → ℕ`; `S j - S (j + 1)` and `n - 1` are natural subtractions. For $\rho = 0$ the first factor is $0$ when the exponent is positive. A choice with integer exponents, for example $h = 2^{4nt}$, $N = 2^{(8n-2)t}$, $S_j = 2^{8nt - j}$, $R_j = 2^{(4n+j)t}$, avoids real powers.
-- source:
--   The choice of parameters in B. Rousseau, Séminaire de Théorie des Nombres de Bordeaux 1968-1969, exposé 11, pp. 3 and 5-7 ($L = [h^{2 - 1/(2n)}]$, orders $h^2/2^J$, points $h^{1 + \varepsilon J}$ with $\varepsilon = 1/(4n)$), and in S. Dasgupta, arXiv:2303.02037, Section 2.4 (bootstrapping). The statement here is the pure existence of parameters that satisfy the conditions of `NumberField.Brumer.exists_int_coeffs_vanishing` and `NumberField.Brumer.extrapolation_step`.

import Mathlib

theorem NumberField.Brumer.exists_parameters (n d q : ℕ) (hn : 0 < n) (hd : 0 < d) (C₁ C₃ ρ : ℝ)
    (h1 : 1 ≤ C₁) (h3 : 1 ≤ C₃) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ (N J : ℕ) (S R : ℕ → ℕ), 0 < N ∧
      2 * d * (S 0 + 1) ^ (n - 1) * R 0 ≤ N ^ n ∧ N ^ n ≤ R J ∧
      ∀ j < J, S (j + 1) ≤ S j ∧
        ρ ^ (R j * (S j - S (j + 1))) *
          ((N : ℝ) ^ n * ((N : ℝ) ^ n * C₁ ^ (N * R 0 + S 0) * (N : ℝ) ^ S 0) *
            C₃ ^ (q * N * R (j + 1) + S (j + 1)) * (N : ℝ) ^ S (j + 1)) ^ d < 1 := by sorry
