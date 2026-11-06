-- Prove2me | Theorems.Thm_GuthMaynard_card_le_mul_topSingularValue_sq
-- name    : GuthMaynard.card_le_mul_topSingularValue_sq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T18:19:23.644266+00:00
-- url     : https://prove2.me/theorems/703deee6-293d-4d63-b2e0-00e19b563b87
-- title:
--   Lemma 4.1 (Large values of Dirichlet polynomials controlled by singular values)
-- statement:
--   Let $w$ be a weight as in §3 (`IsWeight w`). There is a constant $C$ such that for every integer $N \ge 1$, every real $\sigma$, all complex $(b_n)$ with $|b_n| \le 1$, and every finite set $W \subset \mathbb R$: if $|D_N(t)| \ge N^\sigma$ for all $t \in W$, then
--   $$|W| \le C\,N^{1-2\sigma}s_1(M_W)^2.$$
--   Here $D_N(t) = \sum_n w(n/N)\,b_n n^{it}$ (`smoothedPoly w N b t`), $M_W$ is the $|W| \times N$ matrix with entries $w(n/N)\,n^{it}$ for $t \in W$ and $N < n \le 2N$ (`weightMatrix w N W`), and $s_1$ is its largest singular value (`topSingularValue`).
--
--   **Formalization note.** $\ll$ is an absolute constant (§1.2), allowed to depend on the fixed weight $w$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 10, Lemma 4.1 (Large values of Dirichlet polynomials controlled by singular values)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem card_le_mul_topSingularValue_sq (w : ℝ → ℝ) (hw : IsWeight w) :
    ∃ C : ℝ, ∀ (N : ℕ), 1 ≤ N → ∀ (σ : ℝ) (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedPoly w N b t‖) →
      (W.card : ℝ) ≤ C * (N : ℝ) ^ (1 - 2 * σ) * topSingularValue (weightMatrix w N W) ^ 2 := by
  sorry

end GuthMaynard
