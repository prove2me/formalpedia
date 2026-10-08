-- Prove2me | Theorems.Thm_GenericBudgets_AlmostEqual_not_mem_R_of_almost_equal
-- name    : GenericBudgets.AlmostEqual.not_mem_R_of_almost_equal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:48.512404+00:00
-- url     : https://prove2.me/theorems/85a12fdc-eced-47d6-abf1-136994d2a6b1
-- title:
--   Proof of Theorem 7.1, p. 19, last paragraph — almost equal, unequal budgets avoid $R_i$
-- statement:
--   Consider two agents with additive, normalized, non-negative, monotone and strict valuations $v_1,v_2$ on $m$ indivisible items. For each agent $i$ there is $\delta>0$ such that every budget pair $(b_1,b_2)$ with $b_1,b_2>0$, $b_1+b_2=1$ and
--   $$b_2<b_1\le b_2+\delta$$
--   lies outside the exceptional set $R_i(v_1,v_2)$ of Definition 6.2.
--
--   $R_i$ is finite, so it can only meet the half-open interval of almost-equal budgets near $b_1=\tfrac12$ in finitely many points; the strict inequality $b_1>b_2$ excludes the point $b_1=\tfrac12$ itself, which can belong to $R_i$. This is the genericity step that closes the proof of Theorem 7.1 via Lemma 6.3.
--
--   **Formalization Note** "$b_1>b_2$" is `b 1 < b 0`, because the paper's agents 1, 2 are indices 0, 1. $\delta$ depends on the valuations and the agent only, and is chosen before the budgets. Strictness is taken as plain injectivity of each valuation on bundles; the paper's single exception for identical items (p. 6) is dropped, so markets with identical items are excluded.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 19, proof of Theorem 7.1, last paragraph

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.AlmostEqual

theorem not_mem_R_of_almost_equal {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsStandardValuation (v i)) :
    ∀ i : Fin 2, ∃ δ > 0, ∀ b : Fin 2 → ℝ, (∀ j, 0 < b j) → b 0 + b 1 = 1 → b 1 < b 0 →
      b 0 - b 1 ≤ δ → ¬ InR v b i := by sorry
end GenericBudgets.AlmostEqual
