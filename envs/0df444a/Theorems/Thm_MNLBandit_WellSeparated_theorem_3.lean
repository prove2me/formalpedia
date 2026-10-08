-- Prove2me | Theorems.Thm_MNLBandit_WellSeparated_theorem_3
-- name    : MNLBandit.WellSeparated.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:33.846884+00:00
-- url     : https://prove2.me/theorems/a1cab3be-4452-43d4-a67f-2d3cbe53771c
-- title:
--   Theorem 3, p. 20 — on well-separated instances Algorithm 1 has regret at most B₁N² log T/Δ(v) + B₂
-- statement:
--   Consider the MNL-Bandit problem with $N$ products, revenues $r_i\in[0,1]$, and Assumption 4.1: the attraction parameters satisfy $0\le v_i\le v_0=1$, and the feasible family $\mathcal S$ has the totally unimodular form (2.3) and is closed under taking subsets. Let $\Delta(\mathbf v)$ be the separation (6.1) between the expected revenues of the optimal and the second-best assortment.
--
--   There are absolute constants $B_1$ and $B_2$ such that for every such instance, every tie-breaking rule in the argmax of Algorithm 1, and every horizon $T$, the regret of Algorithm 1 satisfies
--   $$
--   \mathrm{Reg}_\pi(T,\mathbf v)\le B_1\,\frac{N^2\log T}{\Delta(\mathbf v)}+B_2.
--   $$
--
--   The worst-case bound of Theorem 1 grows like $\sqrt{T}$. When the optimal assortment is separated from the others, the same algorithm, which does not know $\Delta(\mathbf v)$, has regret logarithmic in $T$.
--
--   **Formalization Note** The constants $B_1,B_2$ are chosen before the number of products, the parameters, the revenues, the feasible family, the tie-breaking rule and the horizon. $\log T$ is stated as printed; the proof's final display (C.12) has $\log NT$, from which the printed form follows. When every feasible assortment is optimal, $\Delta(\mathbf v)$ is a minimum over the empty set. Lean then uses the value $1$; the regret is $0$ in that case. The constraint $v_0=1$ is the paper's normalization (p. 5).
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 20, Theorem 3 (Δ(v) from (6.1), p. 19; proof App. C, pp. 46–50)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-- Theorem 3, p. 20 (arXiv:1706.03880v2): under Assumption 4.1 and `r_i ∈ [0, 1]`, the regret of
Algorithm 1 is at most `B₁ N² log T / Δ(v) + B₂` for absolute constants `B₁, B₂`, for every
tie-breaking rule of the argmax and every horizon `T`. -/
theorem theorem_3 :
    ∃ B₁ B₂ : ℝ, ∀ (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
      (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (T : ℕ),
      MNLBandit.UCB.IsTU 𝒮 → MNLBandit.UCB.DownClosed 𝒮 → (∀ i, 0 ≤ v i ∧ v i ≤ 1) → (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) →
      MNLBandit.UCB.IsArgmaxSel 𝒮 sel →
      MNLBandit.UCB.regret v r 𝒮 h𝒮 (alg1 r sel) T ≤
        B₁ * ((N : ℝ) ^ 2 * Real.log T / gap v r 𝒮 h𝒮) + B₂ := by sorry

end MNLBandit.WellSeparated
