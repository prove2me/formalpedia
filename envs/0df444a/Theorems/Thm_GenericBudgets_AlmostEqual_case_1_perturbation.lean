-- Prove2me | Theorems.Thm_GenericBudgets_AlmostEqual_case_1_perturbation
-- name    : GenericBudgets.AlmostEqual.case_1_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:49.461767+00:00
-- url     : https://prove2.me/theorems/079a3b7d-a643-4d85-b319-de464bcba6dc
-- title:
--   Proof of Theorem 7.1, Case 1, p. 18 — a CE at budgets (1/2, 1/2) survives a small increase of agent 1's budget
-- statement:
--   Consider two agents with valuations $v_1,v_2$ on bundles of $m$ indivisible items. Suppose $(\mathcal S,p)$ is a competitive equilibrium at the equal budgets $b_1=b_2=\tfrac12$. Then there is $\delta>0$ such that for every $\epsilon\in(0,\delta)$ the pair $(\mathcal S,\ p/(1+\epsilon))$ is a competitive equilibrium at the normalized budgets
--   $$b_1=\frac{\tfrac12+\epsilon}{1+\epsilon}>\frac12,\qquad b_2=1-b_1=\frac{\tfrac12}{1+\epsilon}.$$
--   Equivalently, after rescaling prices and budgets by $1+\epsilon$, the original equilibrium remains an equilibrium when agent 1's budget is raised from $\tfrac12$ to $\tfrac12+\epsilon$.
--
--   This is Case 1 of the proof of Theorem 7.1: when some allocation gives both agents exactly $\tfrac12$, a CE at equal budgets exists (Proposition 5.1) and it persists for budgets slightly above equality.
--
--   **Formalization Note** The page writes "as prices have not changed". At the normalized budgets the prices must be divided by $1+\epsilon$: with unchanged budget-exhausting prices agent 2 could no longer afford $\mathcal S_2$, since $p(\mathcal S_2)=\tfrac12>b_2$. The statement uses the rescaled prices, which is the paper's argument made correct. No assumption on the valuations is needed (only finiteness of the item set), so none is imposed. The paper's agents 1, 2 are indices 0, 1.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 18, proof of Theorem 7.1, Case 1

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.AlmostEqual

theorem case_1_perturbation {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (σ : Fin m → Fin 2) (p : Fin m → ℝ) (hCE : IsCE v (fun _ => 1 / 2) σ p) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      IsCE v ![(1 / 2 + ε) / (1 + ε), 1 - (1 / 2 + ε) / (1 + ε)] σ (fun j => p j / (1 + ε)) := by sorry
end GenericBudgets.AlmostEqual
