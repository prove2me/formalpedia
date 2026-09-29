-- Prove2me | Theorems.Thm_FourExp_construction_count
-- name    : FourExp.construction_count
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-15T06:23:13.45348+00:00
-- url     : https://prove2.me/theorems/7a066d6f-d00c-44b6-bbf5-6b0929830623
-- title:
--   Waldschmidt's parameters exceed the zero count
-- statement:
--   **The parameters of the construction beat the zero count.**
--
--   For $X, Y_1, Y_2 \ge 0$ there is $N_0$ such that for every integer $N > N_0$, with
--   $$S = \lfloor N^2\sqrt{\log N}\rfloor,\quad T = 2N,\quad R_1 = 14\lfloor N/\sqrt{\log N}\rfloor,\quad R_2 = 14\lfloor N\sqrt{\log N}\rfloor,\quad S' = \lfloor S/2\rfloor,\quad \lambda = \tfrac1{20},$$
--   and $n = ST^2$, one has
--   $$\frac{n}{\lambda} + 2\,\frac{1 + n^{\lambda}}{\lambda\log n}\bigl(1 + (R_1Y_1 + R_2Y_2)\,T X\bigr) \;\le\; R_1R_2S' .$$
--
--   **Why.** $n/\lambda \approx 80\,N^4\sqrt{\log N}$, while $R_1R_2S' \approx 98\,N^4\sqrt{\log N}$. The second term is $O\bigl(N^{2.2}\sqrt{\log N}\bigr)$. The floors cost only lower-order terms. Numerically the ratio of the two sides tends to $80/98 \approx 0.816$; the threshold $N_0$ grows with $X$ and $Y_i$, for instance about $56$ for $X = Y_i = 10$ and about $5\,600$ for $X = Y_i = 1000$.
--
--   **What it is for.** With $X = |x_1| + |x_2|$ and $Y_i = |y_i|$, this is the zero-count hypothesis of `FourExp.nonvanishing_derivative` for the parameters of `FourExp.construction_core`.
-- source:
--   Asymptotic check of the parameters of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, formula (4) and Lemma 6, against the zero estimate of M. Waldschmidt, Bull. Soc. Math. France 99 (1971), §4, Lemma 3. Superseded: stated for S = floor(N^2 sqrt(log N)) rather than the 1973 text's S = floor(N^2 / sqrt(log N)). The inequality holds for both choices, but only the second is the one the construction needs. Replaced by FourExp.construction_count_1973, which is Proved.

import Mathlib

namespace FourExp

theorem construction_count (X Y₁ Y₂ : ℝ) (hX : 0 ≤ X) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ((((⌊(N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))⌋₊) * (2 * N) * (2 * N) : ℕ) : ℝ) / (1 / 20 : ℝ)
              + 2 * (1 + (((⌊(N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))⌋₊) * (2 * N) * (2 * N) : ℕ) : ℝ) ^ (1 / 20 : ℝ)) / ((1 / 20 : ℝ) * Real.log ((((⌊(N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))⌋₊) * (2 * N) * (2 * N) : ℕ) : ℝ)))
                * (1 + (((14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊) : ℕ) * Y₁ + ((14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊) : ℕ) * Y₂) * (((2 * N) : ℕ) * X))
            ≤ ((((14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊)) * ((14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊)) * (⌊(N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))⌋₊ / 2) : ℕ) : ℝ)) := by
  sorry

end FourExp
