-- Prove2me | Theorems.Thm_GenericBudgets_MaximinShare_proposition_3_2
-- name    : GenericBudgets.MaximinShare.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:54.56409+00:00
-- url     : https://prove2.me/theorems/008cfeff-9286-4372-871e-29c6c2a598e1
-- title:
--   Proposition 3.2 — every equilibrium guarantees every affordable ℓ-out-of-d maximin share
-- statement:
--   Let $N$ be a finite set of agents, $M$ a finite set of indivisible items, and $v_i$ an arbitrary cardinal valuation on bundles for each agent. Let the positive budgets satisfy $\sum_{i\in N}b_i=1$, and let $(S,p)$ be a competitive equilibrium. For any agent $i$ and natural numbers $\ell,d$ with $d>0$ and $\ell/d\le b_i$, the allocated bundle guarantees her $\ell$-out-of-$d$ maximin share:
--
--   $$
--   v_i(S_i)\ge
--   \max_{(T_1,\ldots,T_d)}\;
--   \min_{L\subseteq[d],\,|L|=\ell}
--   v_i\!\left(\bigcup_{t\in L}T_t\right).
--   $$
--
--   Thus equilibrium gives an entitlement-sensitive fairness guarantee for every rational share no larger than an agent's budget, even when preferences are not additive.
--
--   **Formalization Note** The Lean goal uses the equivalent quantified form of the finite max–min formula. Positive normalized budgets are the paper's standing assumptions. No additivity, monotonicity, valuation normalization, or strictness is assumed for this proposition; $0\le\ell\le d$ follows from the displayed budget condition and budget normalization. Partitions may contain empty parts. Lean agents and items are zero-indexed.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 9, Proposition 3.2; §2.1 standing budget assumptions, p. 6

import Mathlib
import Definitions.Def_GenericBudgets_MaximinShare_Setting

namespace GenericBudgets.MaximinShare

/-- Proposition 3.2: every competitive equilibrium gives each agent her
`ℓ`-out-of-`d` maximin share when `ℓ / d` does not exceed her budget. -/
theorem proposition_3_2 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) (hsum : ∑ i, b i = 1)
    (σ : Fin m → Fin n) (p : Fin m → ℝ) (hCE : IsCE v b σ p)
    (i : Fin n) (ℓ d : ℕ) (hd : 0 < d) (hℓd : (ℓ : ℝ) / d ≤ b i) :
    GuaranteesMMS v σ i ℓ d := by sorry

end GenericBudgets.MaximinShare
