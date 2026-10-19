-- Prove2me | Theorems.Thm_LowRankMarkov_RankMLE_ec15_W1_tail
-- name    : LowRankMarkov.RankMLE.ec15_W1_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:16.480182+00:00
-- url     : https://prove2.me/theorems/ea3523b1-97db-4d61-97ef-1eca43141175
-- title:
--   (EC.15), ec10 — ℙ{W_n^{(1)} ≥ nπ_max + (4nA₁π_max ξ log p)^{1/2} + 4A₂ξ log p} ≤ p^{−(ξ−1)}
-- statement:
--   Let $p\ge2$, $\alpha,\beta>0$, and let $X_0,\dots,X_n$ be the Markov chain with transition matrix $P$ satisfying Assumption 1, primitive, started from its stationary distribution $\pi$ (all $\pi_i>0$), with $\rho_+<1$ (Definition 1). Put
--   $$W^{(1)}_n=\max_{j\in[p]}\sum_{i=1}^nP_{X_{i-1},j},\qquad A_1=\frac{1+\max(\rho_+,0)}{1-\max(\rho_+,0)},\qquad A_2=\frac13 1_{\{\rho_+\le0\}}+\frac{5}{1-\rho_+}1_{\{\rho_+>0\}} .$$
--   Then for every $\xi>0$,
--   $$\mathbb P\Big\{W^{(1)}_n\ge n\pi_{\max}+(4nA_1\pi_{\max}\xi\log p)^{1/2}+4A_2\xi\log p\Big\}\le p^{-(\xi-1)} .$$
--
--   $W^{(1)}_n$ is the spectral norm of the predictable quadratic variation $\sum_i\mathbb E(Z_i^\top Z_i\mid X_{i-1})$ of the matrix martingale in the proof of Lemma 3; this tail bound feeds the matrix Freedman inequality there.
--
--   **Formalization Note** The paper derives this from a Bernstein inequality for general Markov chains (Jiang, Fan and Sun 2018, Theorem 1.2), which it cites and does not prove. The chain starts at stationarity ($X_0\sim\pi$). The hypothesis $\rho_+<1$ (Definition 1) makes $A_1,A_2$ finite; Assumption 1 is the section's standing assumption. $\log$ is natural and $p^{-(\xi-1)}$ is a real power.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. ec10 (PDF p. 43), (EC.15); W_n^{(1)} defined p. ec9 (PDF p. 42)

import Mathlib
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting

namespace LowRankMarkov.RankMLE

/-- (EC.15), ec10, arXiv:1907.00113v2: for the stationary chain (`X₀ ∼ π`) with `ρ₊ < 1` and every
`ξ > 0`, `W_n^{(1)} := max_j ∑_{i=1}^n P_{X_{i−1}, j}` satisfies
`ℙ{W_n^{(1)} ≥ nπ_max + (4nA₁π_max ξ log p)^{1/2} + 4A₂ ξ log p} ≤ p^{−(ξ−1)}`, with
`A₁ = (1 + max(ρ₊, 0))/(1 − max(ρ₊, 0))` and `A₂ = (1/3)1{ρ₊ ≤ 0} + (5/(1 − ρ₊))1{ρ₊ > 0}`. -/
theorem ec15_W1_tail {p r n : ℕ} (α β : ℝ) (hp : 2 ≤ p) (hα : 0 < α) (hβ : 0 < β)
    (P : Matrix (Fin p) (Fin p) ℝ) (π : Fin p → ℝ)
    (hP : IsStochastic P) (hπ : IsStationary π P) (hπ_pos : ∀ i, 0 < π i)
    (hprim : IsPrimitive P) (hA1 : Assumption1 α β r P)
    (hgap : rhoPlus π P < 1) (ξ : ℝ) (hξ : 0 < ξ) :
    let A₁ : ℝ := (1 + max (rhoPlus π P) 0) / (1 - max (rhoPlus π P) 0)
    let A₂ : ℝ := (if rhoPlus π P ≤ 0 then 1 / 3 else 0) +
      (if 0 < rhoPlus π P then 5 / (1 - rhoPlus π P) else 0)
    let W1 : (Fin (n + 1) → Fin p) → ℝ := fun x => ⨆ j, ∑ k : Fin n, P (x k.castSucc) j
    trajProb π P (fun x : Fin (n + 1) → Fin p =>
        n * piMax π + Real.sqrt (4 * n * A₁ * piMax π * ξ * Real.log p) + 4 * A₂ * ξ * Real.log p
          ≤ W1 x) ≤ (p : ℝ) ^ (-(ξ - 1)) := by sorry

end LowRankMarkov.RankMLE
