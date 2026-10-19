-- Prove2me | Theorems.Thm_LargeBSP_Homog_Vbar_eq_integral_empQuantile
-- name    : LargeBSP.Homog.Vbar_eq_integral_empQuantile
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:51.885996+00:00
-- url     : https://prove2.me/theorems/d6f7748e-c687-445f-b519-62b1e360bf4e
-- title:
--   Proof of Theorem 2, p. A2 — V̄_N(n/N) = ∫_0^{n/N} 𝔽^{-1}_{X,N}(1 − s) ds
-- statement:
--   Let $x_1, x_2, \dots \ge 0$, $N \ge 1$ and $0 \le n \le N$. Then
--   $$\bar V_N\!\left(\tfrac nN\right) = \int_0^{n/N} \mathbb F^{-1}_{x,N}(1-s)\,ds,$$
--   where $\bar V_N(t) = \frac1N V_N(\lfloor Nt \rfloor)$ is the normalized value of the top $\lfloor Nt \rfloor$ items and $\mathbb F^{-1}_{x,N}$ is the empirical quantile function of $x_1, \dots, x_N$.
--
--   It expresses a sum of top order statistics as an integral of the empirical quantile function, which is how the proof of Theorem 2 passes to the limit.
--
--   **Formalization Note** The page states the identity "for $0 \le t \le 1$". It is exact only at the grid points $t = n/N$: off the grid the right side exceeds the left by $(t - \lfloor Nt \rfloor/N)\,X_{(N - \lfloor Nt\rfloor)}$ (e.g. $N = 1$, $x_1 = 1$, $t = 1/2$: left $0$, right $1/2$). The Lean statement is the grid version, which is what the page's argument yields.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), proof of Theorem 2 (Appendix A.1), p. A2, display after (A6)

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

namespace LargeBSP.Homog

/-- Proof of Theorem 2, p. A2: `V̄_N(t) = ∫_0^t 𝔽⁻¹_{X,N}(1 − s) ds`, at the grid points
`t = n/N`, `n = 0, …, N` (off the grid the page's identity is false; see the notes). -/
theorem Vbar_eq_integral_empQuantile (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n) (N : ℕ) (hN : 1 ≤ N)
    (n : ℕ) (hn : n ≤ N) :
    Vbar x N ((n : ℝ) / N) = ∫ s in (0 : ℝ)..((n : ℝ) / N), quantile (empCdf x N) (1 - s) := by sorry

end LargeBSP.Homog
