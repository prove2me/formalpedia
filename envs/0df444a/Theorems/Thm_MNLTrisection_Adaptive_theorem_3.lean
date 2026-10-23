-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_theorem_3
-- name    : MNLTrisection.Adaptive.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:58.106594+00:00
-- url     : https://prove2.me/theorems/a6a3dbbc-4913-4fc4-9209-5e9e3e174da4
-- title:
--   Theorem 3, p. 12 — the adaptive-confidence trisection policy has regret at most C₁√T, for a universal C₁ independent of N, v and r
-- statement:
--   Throughout, there are $N$ items with known revenues $r_i \in [0,1]$ and unknown utilities $v_i \ge 0$, the no-purchase utility is $v_0 = 1$, and $R(S) = \sum_{j\in S} r_j v_j/(1+\sum_{j\in S} v_j)$ is the expected revenue (2) of an assortment $S \subseteq [N]$. The adaptive-confidence trisection policy (Algorithm 1 with the EXPLORE subroutine of Algorithm 2, confidence intervals $\rho_t/t \pm \sqrt{2\ln(8T/t)/t}$ and $n_\tau = 8\lceil\varepsilon_\tau^{-2}\ln(8T\varepsilon_\tau^2)\rceil$ inner iterations per epoch) knows only $r$ and $T$. There is a universal constant $C_1 > 0$ such that for every $N$, every horizon $T$, all $v_i \ge 0$ and all $r_i \in [0,1]$,
--   $$\mathrm{Regret}(\{S_t\}_{t=1}^T) = \mathbb E\sum_{t=1}^T R(S^*) - R(S_t) \le C_1\sqrt T,$$
--   where $S^*$ maximizes $R$ over all subsets of $[N]$.
--
--   The bound is independent of the number of items and of the utilities, and matches the lower bound $\sqrt T/384$ of Theorem 4 up to a constant.
--
--   **Formalization Note** The regret is that of the published `MNLBandit.UCB.Setting` with all subsets admissible. $C_1$ is chosen before $N$, $T$, $v$ and $r$. The policy is a function of $r$, $T$ and the observed choices only. Its inner-iteration count is $\max(1, n_\tau)$, and it may offer the empty level set (revenue $0$), which §3's $S_t \neq \varnothing$ excludes; the paper's $r_i > 0$ is relaxed to Theorem 3's $r_i \in [0,1]$.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, p. 12, Theorem 3, Eq. (13)

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

open MNLBandit.UCB

/-- **Theorem 3** (p. 12). There is a universal constant `C₁ > 0` such that for every number of
items `N`, every horizon `T`, all utilities `v_i ≥ 0` and all revenues `r_i ∈ [0, 1]`, the
adaptive-confidence trisection policy has regret (13)
`𝔼 ∑_{t=1}^T R(S*) − R(S_t) ≤ C₁ √T`, where `S*` maximizes `R` over all assortments. -/
theorem theorem_3 :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (N T : ℕ) (v r : Fin N → ℝ), (∀ i, 0 ≤ v i) →
      (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) →
      regret v r (Finset.univ : Finset (Finset (Fin N))) ⟨∅, Finset.mem_univ _⟩
        (adaptivePolicy r T) T ≤ C₁ * Real.sqrt T := by sorry

end MNLTrisection.Adaptive
