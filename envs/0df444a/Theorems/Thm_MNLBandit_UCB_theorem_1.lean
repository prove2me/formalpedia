-- Prove2me | Theorems.Thm_MNLBandit_UCB_theorem_1
-- name    : MNLBandit.UCB.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:53:22.790463+00:00
-- url     : https://prove2.me/theorems/9f2bbcd0-cd9c-4c39-b074-8bc881077db6
-- title:
--   Theorem 1, p. 11 — Algorithm 1 has regret at most C₁√(NT log NT) + C₂N log² NT
-- statement:
--   **Performance bound for Algorithm 1.** There are absolute constants $C_1$ and $C_2$ with the following property. Consider any instance of the MNL-Bandit problem:
--   1. $N$ products with revenues $r_i\in[0,1]$;
--   2. MNL parameters $0\le v_i\le v_0=1$ (Assumption 4.1.1);
--   3. a nonempty feasible family $\mathcal S$ of the form (2.3), $\{S : A\,x(S)\le b\}$ with $A$ totally unimodular and $b$ integral, closed under taking subsets (Assumption 4.1.2).
--
--   Let $\pi$ be Algorithm 1 run with any argmax tie-breaking rule. Then for every horizon $T$,
--   $$
--   \mathrm{Reg}_\pi(T,v)=T\,R(S^*,v)-\mathbb E_\pi\Big[\sum_{t=1}^TR(S_t,v)\Big]\le C_1\sqrt{NT\log NT}+C_2N\log^2NT .
--   $$
--   The algorithm does not know $v$: it uses only the revenues, the feasible family and the observed choices. The bound holds without any separation between the optimal and the suboptimal assortments.
--
--   **Formalization Note.** The constants are quantified before every other object (number of products, horizon, parameters, revenues, family and tie-breaking rule), so they are uniform as the page says. $\log$ is the natural logarithm. At $NT\le1$ the right side is $0$, and so is the regret (with one product and one customer the first assortment is already optimal). The nonemptiness of $\mathcal S$ is presupposed by the paper's $S^*=\operatorname{argmax}_{S\in\mathcal S}R(S,v)$.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 11, Theorem 1 and Assumption 4.1

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

theorem theorem_1 :
    ∃ C₁ C₂ : ℝ, ∀ (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
      (hne : 𝒮.Nonempty) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (T : ℕ),
      IsTU 𝒮 → DownClosed 𝒮 → IsArgmaxSel 𝒮 sel →
      (∀ i, 0 ≤ v i) → (∀ i, v i ≤ 1) → (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) →
      regret v r 𝒮 hne (alg1 r sel) T ≤
        C₁ * Real.sqrt (N * T * Real.log (N * T)) + C₂ * N * Real.log (N * T) ^ 2 := by sorry

end MNLBandit.UCB
