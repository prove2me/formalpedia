-- Prove2me | Theorems.Thm_LowRankMarkov_RankMLE_ec17_W2_tail
-- name    : LowRankMarkov.RankMLE.ec17_W2_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:14.314909+00:00
-- url     : https://prove2.me/theorems/cc9fe0c9-c509-494c-8655-cfc44011fac6
-- title:
--   (EC.17), ec10 — ℙ{W_n^{(2)} ≥ nπ_max + (4nA₁π_max ξ log p)^{1/2} + 4A₂ξ log p} ≤ p^{−(ξ−1)}
-- statement:
--   Let $p\ge2$, $\alpha,\beta>0$, and let $X_0,\dots,X_n$ be the Markov chain with transition matrix $P$ satisfying Assumption 1, primitive, started from its stationary distribution $\pi$ (all $\pi_i>0$), with $\rho_+<1$ (Definition 1). Put
--   $$W^{(2)}_n=\max_{j\in[p]}\sum_{i=1}^n1_{\{X_{i-1}=s_j\}},$$
--   the largest number of visits to a single state among $X_0,\dots,X_{n-1}$, and let $A_1,A_2$ be as in (EC.15). Then for every $\xi>0$,
--   $$\mathbb P\Big\{W^{(2)}_n\ge n\pi_{\max}+(4nA_1\pi_{\max}\xi\log p)^{1/2}+4A_2\xi\log p\Big\}\le p^{-(\xi-1)} .$$
--
--   $W^{(2)}_n$ is the spectral norm of the other predictable quadratic variation $\sum_i\mathbb E(Z_iZ_i^\top\mid X_{i-1})$ of the matrix martingale in the proof of Lemma 3.
--
--   **Formalization Note** As for (EC.15), the paper derives this from the Bernstein inequality of Jiang, Fan and Sun (2018, Theorem 1.2), which it cites. $X_0\sim\pi$; the hypothesis $\rho_+<1$ makes $A_1,A_2$ finite; Assumption 1 is the section's standing assumption.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. ec10 (PDF p. 43), (EC.16)–(EC.17); W_n^{(2)} defined p. ec9 (PDF p. 42)

import Mathlib
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting

namespace LowRankMarkov.RankMLE

/-- (EC.17), ec10, arXiv:1907.00113v2: for the stationary chain (`X₀ ∼ π`) with `ρ₊ < 1` and every
`ξ > 0`, `W_n^{(2)} := max_j ∑_{i=1}^n 1{X_{i−1} = s_j}` satisfies
`ℙ{W_n^{(2)} ≥ nπ_max + (4nA₁π_max ξ log p)^{1/2} + 4A₂ ξ log p} ≤ p^{−(ξ−1)}`, with `A₁, A₂` as in
(EC.15). -/
theorem ec17_W2_tail {p r n : ℕ} (α β : ℝ) (hp : 2 ≤ p) (hα : 0 < α) (hβ : 0 < β)
    (P : Matrix (Fin p) (Fin p) ℝ) (π : Fin p → ℝ)
    (hP : IsStochastic P) (hπ : IsStationary π P) (hπ_pos : ∀ i, 0 < π i)
    (hprim : IsPrimitive P) (hA1 : Assumption1 α β r P)
    (hgap : rhoPlus π P < 1) (ξ : ℝ) (hξ : 0 < ξ) :
    let A₁ : ℝ := (1 + max (rhoPlus π P) 0) / (1 - max (rhoPlus π P) 0)
    let A₂ : ℝ := (if rhoPlus π P ≤ 0 then 1 / 3 else 0) +
      (if 0 < rhoPlus π P then 5 / (1 - rhoPlus π P) else 0)
    let W2 : (Fin (n + 1) → Fin p) → ℝ := fun x =>
      ⨆ j, ((Finset.univ.filter fun k : Fin n => x k.castSucc = j).card : ℝ)
    trajProb π P (fun x : Fin (n + 1) → Fin p =>
        n * piMax π + Real.sqrt (4 * n * A₁ * piMax π * ξ * Real.log p) + 4 * A₂ * ξ * Real.log p
          ≤ W2 x) ≤ (p : ℝ) ^ (-(ξ - 1)) := by sorry

end LowRankMarkov.RankMLE
