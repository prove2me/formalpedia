-- Prove2me | Theorems.Thm_LinExchangeSP_ZPlus_lemma_7_1
-- name    : LinExchangeSP.ZPlus.lemma_7_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:37.157137+00:00
-- url     : https://prove2.me/theorems/0d747c15-3759-4ea7-8bcb-0d480a3e4928
-- title:
--   Lemma 7.1, p. 16 — on P_M, Mp̄ ≥ −λ ≥ −(B − 1)γ for a Z₊-matrix M
-- statement:
--   Let $M \in \mathcal{Z}_+(t,t)$ be a square $Z_+$-matrix with $t \ge 1$, and let $\gamma \in \mathbb{Q}^t$ with $\gamma > 0$. Put $\lambda_i = \sum_{j\ne i}\gamma_j$ and $B = \sum_{j=1}^t \gamma_j / \min_{i\in[t]}\gamma_i$. If $\bar p \in \mathbb{R}^t_+$ satisfies $M\bar p \le \gamma$, then
--
--   $$M\bar p \ \ge\ -\lambda\ \ge\ -(B-1)\gamma$$
--
--   componentwise.
--
--   The lemma gives a lower bound on every constraint of $P_M$; the constraints of the approximating M2VPI system are nonnegative combinations of these lower bounds.
--
--   **Formalization Note** $\gamma > 0$ is the standing assumption of §7 (p. 16, "$\gamma \in \mathbb{Q}^k$, $\gamma > 0$"); it is needed for the second inequality. $t \ge 1$ is needed for $B$. The positive-diagonal assumption of §7 is not needed and is not imposed.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 16, Lemma 7.1

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting

namespace LinExchangeSP.ZPlus

/-- Lemma 7.1 (p. 16): for `M ∈ Z₊(t, t)`, `γ > 0` and `p̄ ≥ 0` with `Mp̄ ≤ γ`, every row satisfies
`M_i p̄ ≥ -λ_i ≥ -(B - 1)γ_i`, with `λ_i = ∑_{j ≠ i} γ_j` and `B = ∑ⱼ γⱼ / minᵢ γᵢ`. -/
theorem lemma_7_1 {t : ℕ} (ht : 0 < t) (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (γ : Fin t → ℚ) (hγ : ∀ i, 0 < γ i) (p : Fin t → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hMp : ∀ i, rowVal M p i ≤ (γ i : ℝ)) :
    ∀ i, -((lam γ i : ℚ) : ℝ) ≤ rowVal M p i ∧
      -((Bconst γ ht - 1) * (γ i : ℝ)) ≤ -((lam γ i : ℚ) : ℝ) := by sorry

end LinExchangeSP.ZPlus
