-- Prove2me | Theorems.Thm_GenericBudgets_AlmostEqual_proposition_4_1
-- name    : GenericBudgets.AlmostEqual.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:33.672201+00:00
-- url     : https://prove2.me/theorems/2ef1e044-7d05-4f27-afb3-1df6baf1932e
-- title:
--   Proposition 4.1 — characterization of CE for a PO allocation with budget-exhausting prices
-- statement:
--   Let two agents have monotone cardinal valuations $v_1,v_2$ on bundles of $m$ indivisible items (monotone: $v_i(S)<v_i(T)$ whenever $S\subsetneq T$), and positive budgets $b_1,b_2$. Let $\mathcal S=(\mathcal S_1,\mathcal S_2)$ be a Pareto optimal allocation in which both bundles are non-empty, and let $p\ge 0$ be budget-exhausting item prices, $p(\mathcal S_i)=b_i$. Then $(\mathcal S,p)$ is a competitive equilibrium if and only if for $i\ne k$ and every two bundles $S\subseteq\mathcal S_i$, $T\subseteq\mathcal S_k$,
--   $$v_i(S\mid\mathcal S_i\setminus S)>v_i(T\mid\mathcal S_i\setminus S)\ \text{ and }\ v_k(S\mid\mathcal S_k\setminus T)>v_k(T\mid\mathcal S_k\setminus T)\ \Longrightarrow\ p(S)>p(T). \tag{1}$$
--   Here $v(S\mid T)=v(S\cup T)-v(T)$ is the marginal value.
--
--   The characterization holds beyond additive valuations and reduces the verification of a CE to pairwise swaps of sub-bundles between the two agents. It is the basis of Lemma 4.3.
--
--   **Formalization Note** Only monotonicity of the valuations is assumed, as on the page; additivity, normalization and strictness are not. Prices are assumed non-negative as part of the paper's notion of a price vector. The paper's agents 1, 2 are indices 0, 1.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 10, Proposition 4.1

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.AlmostEqual

theorem proposition_4_1 {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hmono : ∀ i, ∀ S T : Finset (Fin m), S ⊂ T → v i S < v i T)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i)
    (σ : Fin m → Fin 2) (hPO : IsPO v σ) (hne : ∀ i, (bundle σ i).Nonempty)
    (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) (hex : IsBudgetExhausting b σ p) :
    IsCE v b σ p ↔ Condition1 v σ p := by sorry
end GenericBudgets.AlmostEqual
