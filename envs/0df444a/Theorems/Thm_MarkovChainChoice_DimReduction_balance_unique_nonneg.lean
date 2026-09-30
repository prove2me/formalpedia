-- Prove2me | Theorems.Thm_MarkovChainChoice_DimReduction_balance_unique_nonneg
-- name    : MarkovChainChoice.DimReduction.balance_unique_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T09:50:43.530854+00:00
-- url     : https://prove2.me/theorems/2d689ccf-6836-4fc4-b2d5-156a55999811
-- title:
--   Section 2 — the (Balance) equations have a unique and nonnegative solution
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model with $\lambda_j>0$, $\rho_{j,i}\ge0$ and $\sum_{i\in N}\rho_{j,i}<1$ for all $j,i\in N$, and let $S\subseteq N$ be any offer set. Then the (Balance) equations
--   $$
--   P_{j}+R_{j}=\lambda_j+\sum_{i\in N}\rho_{i,j}R_{i}\ \ \forall j\in N,\qquad P_{j}=0\ \ \forall j\notin S,\qquad R_{j}=0\ \ \forall j\in S
--   $$
--   have exactly one solution $(P_S,R_S)$, and this solution is nonnegative: $P_{j,S}\ge0$ and $R_{j,S}\ge0$ for all $j\in N$.
--
--   This guarantees that the purchase probabilities $P_S$ and visit counts $R_S$ used by every other statement of the mission are well defined.
--
--   **Formalization Note** The conclusion is stated for the chosen solution `(purchase M S, visitNot M S)`: it solves (Balance), it is nonnegative, and every solution of (Balance) equals it.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1325, Section 2, last sentence of the left column continuing into the right column

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
import Definitions.Def_MarkovChainChoice_Shared_Balance
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

theorem balance_unique_nonneg {n : ℕ} (M : Model n) (S : Finset (Fin n)) :
    IsBalance M S (purchase M S) (visitNot M S) ∧
    (∀ j, 0 ≤ purchase M S j) ∧ (∀ j, 0 ≤ visitNot M S j) ∧
    ∀ P R : Fin n → ℝ, IsBalance M S P R → P = purchase M S ∧ R = visitNot M S := by sorry

end MarkovChainChoice.DimReduction
