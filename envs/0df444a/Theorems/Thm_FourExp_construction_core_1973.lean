-- Prove2me | Theorems.Thm_FourExp_construction_core_1973
-- name    : FourExp.construction_core_1973
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-16T12:09:24.098286+00:00
-- url     : https://prove2.me/theorems/41291ef0-fcbe-4551-92c0-bddd04ee2f84
-- title:
--   The auxiliary function of Waldschmidt 1973, with the paper's derivative range
-- statement:
--   **The analytic-arithmetic core, with the parameters of the 1973 paper.**
--
--   Let $x_1, x_2$ be $\mathbb{Q}$-linearly independent, and likewise $y_1, y_2$. Suppose every $e^{x_iy_j}$ is algebraic and $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}[x_1,x_2,y_1,y_2] \le 1$. Then there are a transcendental $\omega$ and $k > 0$ such that for every $C$ and every large $N$, with
--   $$S = \lfloor N^2/\sqrt{\log N}\rfloor,\quad T = 2N,\quad t_1 = \lfloor N/\sqrt{\log N}\rfloor,\quad t_2 = \lfloor N\sqrt{\log N}\rfloor,\quad R_1 = 14t_1,\quad R_2 = 14t_2,\quad S' = \lfloor S/2\rfloor.$$
--   there are coefficients $c(i,j,k')$, not all zero, with the following property. Put
--   $$F(z) = \sum_{i<S}\ \sum_{j,k'<2N} c(i,j,k')\, z^i\, e^{(jx_1+k'x_2)z}.$$
--   Every non-zero $F^{(s)}(ay_1+by_2)$ with $a<R_1$, $b<R_2$, $s<S'$ yields a non-zero $P \in \mathbb{Z}[X]$ with coefficients at most $e^{\sigma_1(N)}$, $\deg P \le \sigma_2(N)$ and $|P(\omega)| < e^{-C\sigma_1(N)\sigma_2(N)}$. Here $\sigma_1 = kN^2\sqrt{\log N}$ and $\sigma_2 = kN^2/\sqrt{\log N}$ for $N > 3$.
--
--   **Why this node exists.** It restates `FourExp.construction_core` with $S = \lfloor N^2/\sqrt{\log N}\rfloor$. That is the paper's $s_0 = [t_0^2(\log t_0)^{-1/2}]$, from §III (1) and formula (4). The earlier node used $\lfloor N^2\sqrt{\log N}\rfloor$. With that value the degree and the log-height of the polynomials the construction produces grow faster than $\sigma_2$ and $\sigma_1$ for any fixed $k$. The earlier node is left as it is.
--
--   **Proof plan.** A reduction to `FourExp.trdeg_one_presentation`, `FourExp.auxiliary_function`, `FourExp.extrapolation` and `FourExp.norm_to_polynomial`.
--
--   **About the hypotheses.** They are contradictory: that is the four exponentials theorem in transcendence degree one, which this subtree proves. This node is a step of that proof by contradiction, so its proof must not use the theorem.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, §III, formula (4) and Lemmas 4, 5, 7.

import Mathlib

namespace FourExp

theorem construction_core_1973
    (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂]) (hy : LinearIndependent ℚ ![y₁, y₂])
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂} : Set ℂ)) ≤ 1) :
    ∃ ω : ℂ, Transcendental ℚ ω ∧ ∃ k : ℝ, 0 < k ∧
      ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
        ∃ c : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → ℂ, (∃ i j k', c i j k' ≠ 0) ∧
          ∀ a b s : ℕ, a < (14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊) → b < (14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊) → s < (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ / 2) →
            iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
              ((a : ℂ) * y₁ + (b : ℂ) * y₂) ≠ 0 →
            ∃ P : Polynomial ℤ, P ≠ 0 ∧
              (∀ i : ℕ, |(P.coeff i : ℝ)| ≤ Real.exp (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
              (P.natDegree : ℝ) ≤ k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))) ∧
              ‖Polynomial.aeval ω P‖ < Real.exp (-(C * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ)))))) := by
  sorry

end FourExp
