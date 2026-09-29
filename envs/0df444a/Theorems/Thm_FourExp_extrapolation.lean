-- Prove2me | Theorems.Thm_FourExp_extrapolation
-- name    : FourExp.extrapolation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-16T12:09:29.130692+00:00
-- url     : https://prove2.me/theorems/478273e3-7383-4cf2-98e8-dd6ab2db30f3
-- title:
--   Extrapolation from the vanishing grid (Waldschmidt 1973, Lemma 5)
-- statement:
--   **Small derivatives on a larger grid.** Let $x_1, x_2 \in \mathbb{C}$ and let $y_1, y_2$ be $\mathbb{Q}$-linearly independent. For every $\kappa > 0$ there are $\kappa' > 0$ and $N_0$ such that for every $N > N_0$ the following holds, with
--   $$S = \lfloor N^2/\sqrt{\log N}\rfloor,\quad T = 2N,\quad t_1 = \lfloor N/\sqrt{\log N}\rfloor,\quad t_2 = \lfloor N\sqrt{\log N}\rfloor,\quad R_1 = 14t_1,\quad R_2 = 14t_2,\quad S' = \lfloor S/2\rfloor.$$
--   Suppose the coefficients satisfy $|c(i,j,k')| \le e^{\kappa N^2\sqrt{\log N}}$ and $F^{(m)}(ay_1+by_2) = 0$ for $a<t_1$, $b<t_2$, $m<S$, where
--   $$F(z) = \sum_{i<S}\ \sum_{j,k'<2N} c(i,j,k')\, z^i\, e^{(jx_1+k'x_2)z}.$$
--   Then $|F^{(s)}(ay_1+by_2)| \le \exp(-N^4\sqrt{\log N}/\kappa')$ for all $s<S'$, $a<R_1$, $b<R_2$.
--
--   **Proof sketch.** For $s < S/2$, $F^{(s)}$ vanishes to order at least $S/2$ at the $t_1t_2 \approx N^2$ points of the small grid. Apply `FourExp.cauchy_estimate_with_zeros` (Proved) on a disc of radius $NS$ around the target point, bounding $F^{(s)}$ there by Cauchy's estimate. The zeros gain $\approx t_1t_2\,(S/2)\log N^2 \approx N^4\sqrt{\log N}$. The cost is $S\log S + O(N\cdot NS) = O(N^4/\sqrt{\log N})$.
--
--   A purely analytic lemma; $x_1, x_2$ are arbitrary.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Lemma 5.

import Mathlib

namespace FourExp

theorem extrapolation
    (x₁ x₂ y₁ y₂ : ℂ) (hy : LinearIndependent ℚ ![y₁, y₂]) (κ : ℝ) (hκ : 0 < κ) :
    ∃ κ' : ℝ, 0 < κ' ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ c : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → ℂ,
      (∀ i j k', ‖c i j k'‖ ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) →
      (∀ a b m : ℕ, a < ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ → m < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ →
        iteratedDeriv m (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂) = 0) →
      ∀ s : ℕ, s < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ / 2 → ∀ a b : ℕ, a < 14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < 14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ →
        ‖iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂)‖
          ≤ Real.exp (-(((N : ℝ) ^ 4 * Real.sqrt (Real.log (N : ℝ))) / κ')) := by
  sorry

end FourExp
