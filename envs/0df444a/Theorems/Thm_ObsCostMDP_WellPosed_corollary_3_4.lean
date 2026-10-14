-- Prove2me | Theorems.Thm_ObsCostMDP_WellPosed_corollary_3_4
-- name    : ObsCostMDP.WellPosed.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:38.351538+00:00
-- url     : https://prove2.me/theorems/f3a0057f-8785-4df5-86c1-e85dc71be214
-- title:
--   Corollary 3.4 — bounded solutions of the observation cost QVI (2.11) are unique
-- statement:
--   Let $X$, $A$ be finite and nonempty, $\{P_a\}_{a\in A}$ stochastic matrices on $X$, $r:X\times A\to\mathbb R$, $\gamma\in(0,1)$ and $c_{\mathrm{obs}}>0$. If $v$ and $w$ are bounded solutions of the observation cost QVI (2.11),
--
--   $$\min\Big\{v^n_{a,x}-\gamma v^{n+1}_{a,x}-\big(P^n_a r_a\big)_x,\;v^n_{a,x}-\big(P^n_a\,\overline{\gamma v^1+r}\big)_x+c_{\mathrm{obs}}\Big\}=0,\qquad n\ge1,\ x\in X,\ a\in A,$$
--
--   then $v^n_{a,x}=w^n_{a,x}$ for all $n\ge1$, $x\in X$, $a\in A$.
--
--   So the value function of the discounted infinite-horizon observation cost model is characterised as the unique bounded solution of its QVI.
--
--   **Formalization Note** "Bounded" is added: without it the uniqueness fails (with one state and one action, $v^n=r/(1-\gamma)+K\gamma^{-n}$ solves (2.11) for every $K\ge0$). The QVI (2.11) is stated directly, not through the paper's casting into (3.1). The time-$0$ slice is not constrained by (2.11) and is not compared.
-- source:
--   Reisinger & Tam, Markov decision processes with observation costs: framework and computation with a penalty scheme, arXiv:2201.07908v3, p. 16, Corollary 3.4; p. 12, (2.11)

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI
import Definitions.Def_ObsCostMDP_WellPosed_OCM

namespace ObsCostMDP.WellPosed

/-- **Corollary 3.4** (Reisinger–Tam, arXiv:2201.07908v3, p. 16), uniqueness for the OCM QVI (2.11)
(p. 12). Let `γ ∈ (0, 1)`, `c_obs > 0`, every `P_a` a stochastic matrix and `r : X × A → ℝ`. Two
bounded solutions `v, w` of (2.11) (which holds for all `n ≥ 1`) agree at every `n ≥ 1`.
**Formalization Note**: "bounded" is added; without it the statement is false (one state, one
action: `v^n = r/(1 − γ) + Kγ^{−n}`, `K ≥ 0`, all solve (2.11)). The time-`0` slice is not
constrained by (2.11) and is excluded from the conclusion. -/
theorem corollary_3_4 {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : A → Matrix X X ℝ) (hP : ∀ a, IsStochastic (P a)) (r : X → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (cobs : ℝ) (hcobs : 0 < cobs)
    (v w : ℕ → X → A → ℝ) (hv : IsBounded v) (hw : IsBounded w)
    (hvs : IsOCMSolution P r γ cobs v) (hws : IsOCMSolution P r γ cobs w) :
    ∀ n, 1 ≤ n → v n = w n := by sorry

end ObsCostMDP.WellPosed
