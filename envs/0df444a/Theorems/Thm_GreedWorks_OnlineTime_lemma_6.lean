-- Prove2me | Theorems.Thm_GreedWorks_OnlineTime_lemma_6
-- name    : GreedWorks.OnlineTime.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:05:36.512278+00:00
-- url     : https://prove2.me/theorems/b8f5ce5f-6323-4489-b765-d6b928311ec8
-- title:
--   Lemma 6, p. 13 — the greedy schedule satisfies ALG ≤ Σ_j cost(j → m(j))
-- statement:
--   Consider deterministic processing times $p_{ij}\ge1$ on the eligible machine–job pairs, integer release dates $r_j$ with jobs indexed in release order, weights $w_j\ge0$, and a parameter $c>0$. Let $(m,s)$ be any outcome of the online-time greedy algorithm with parameter $c$, where $m(j)$ is the machine to which job $j$ was assigned and $C_j=s_j+p_{m(j)j}$. Then
--   $$\mathsf{ALG}=\sum_{j\in J}w_jC_j\;\le\;\sum_{j\in J}\operatorname{cost}(j\to m(j)).$$
--
--   The quantities $\operatorname{cost}(j\to m(j))$ are the dual values $\alpha_j$ of the dual-fitting argument, so this inequality is where the algorithm's cost enters the analysis.
--
--   **Formalization Note** The statement holds for every tie-breaking of the algorithm and for every $c>0$. $p_{ij}\ge1$ is the paper's scaling assumption $\mathbb E[P_{ij}]\ge1$ (p. 6) and $w\ge0$ is implicit on the page.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 13, Lemma 6

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Greedy

namespace GreedWorks.OnlineTime

/-- Lemma 6 (p. 13). For deterministic processing times (`p_ij ≥ 1` on eligible pairs), every
parameter `c > 0` and every outcome `(m, s)` of the online-time greedy algorithm, the objective
value `ALG = Σ_j w_j C_j` is at most `Σ_j cost(j → m(j))`. -/
theorem lemma_6 {M : Type*} [Fintype M] [Nonempty M] {n : ℕ}
    (elig : M → Fin n → Prop) (hElig : ∀ j, ∃ i, elig i j)
    (r : Fin n → ℕ) (hr : Monotone r)
    (p : M → Fin n → ℝ) (hp : ∀ i j, elig i j → 1 ≤ p i j)
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (c : ℝ) (hc : 0 < c) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy c r p w elig m s) :
    nominalValue p w m s ≤ ∑ j : Fin n, cost c r p w m s j (m j) := by sorry

end GreedWorks.OnlineTime
