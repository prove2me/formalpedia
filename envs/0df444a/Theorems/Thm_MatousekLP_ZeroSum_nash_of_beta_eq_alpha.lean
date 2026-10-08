-- Prove2me | Theorems.Thm_MatousekLP_ZeroSum_nash_of_beta_eq_alpha
-- name    : MatousekLP.ZeroSum.nash_of_beta_eq_alpha
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:16:48.26652+00:00
-- url     : https://prove2.me/theorems/f26fac4d-3f68-4e22-8471-9b852da4abcf
-- title:
--   Lemma 8.1.2(iii) — β(x̃) = α(ỹ) implies a mixed Nash equilibrium
-- statement:
--   Let $M$ be a real $m \times n$ payoff matrix of a zero-sum game, $m, n \ge 1$. If mixed strategies $\tilde{\mathbf x}$ of Alice and $\tilde{\mathbf y}$ of Bob satisfy
--   $$
--   \beta(\tilde{\mathbf x}) = \alpha(\tilde{\mathbf y}),
--   $$
--   then $(\tilde{\mathbf x}, \tilde{\mathbf y})$ is a mixed Nash equilibrium: $\tilde{\mathbf x}$ is a best response against $\tilde{\mathbf y}$ and $\tilde{\mathbf y}$ is a best response against $\tilde{\mathbf x}$.
--
--   This is the step that turns the equality of the optimal values of two dual linear programs into an equilibrium in the proof of the minimax theorem.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 136, Lemma 8.1.2(iii)

import Mathlib
import Definitions.Def_MatousekLP_ZeroSum_Game

namespace MatousekLP.ZeroSum

theorem nash_of_beta_eq_alpha {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) (xt : Fin m → ℝ) (yt : Fin n → ℝ)
    (hx : xt ∈ stdSimplex ℝ (Fin m)) (hy : yt ∈ stdSimplex ℝ (Fin n))
    (h : beta M xt = alpha M yt) :
    IsMixedNash M xt yt := by sorry

end MatousekLP.ZeroSum
