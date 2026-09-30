-- Prove2me | Theorems.Thm_MarkovChainChoice_Reduced_balance_unique_nonneg
-- name    : MarkovChainChoice.Reduced.balance_unique_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:31:48.76177+00:00
-- url     : https://prove2.me/theorems/119abadb-d858-4a87-90bc-b574cc85d7f4
-- title:
--   Section 2, p. 1325 — (Balance) has a unique and nonnegative solution for every offer set
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model with $\lambda_j>0$, $\rho_{j,i}\ge 0$ and $\sum_{i\in N}\rho_{j,i}<1$ for all $j\in N$. Then for every offer set $S\subseteq N$ the (Balance) equations
--   $$P_{j} + R_{j} = \lambda_j + \sum_{i\in N}\rho_{i,j}R_{i}\ \ \forall j\in N,\qquad P_{j} = 0\ \ \forall j\notin S,\qquad R_{j} = 0\ \ \forall j\in S$$
--   have exactly one solution $(P,R)$, and this solution is nonnegative. We denote it $(P_S,R_S)$.
--
--   This is what makes the purchase probabilities $P_{j,S}$ well defined; every later statement about $(P_S,R_S)$ relies on it.
--
--   **Formalization Note** The statement says that the chosen pair (`purchase M S`, `visitNot M S`) satisfies (Balance), is componentwise nonnegative, and equals every solution of (Balance).
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1325, Section 2 (last sentence of the paragraph on (I − Q̄)^T R̄_S = λ̄)

import Mathlib
import Definitions.Def_MarkovChainChoice_Reduced_Model

namespace MarkovChainChoice.Reduced

theorem balance_unique_nonneg {n : ℕ} (M : Model n) (S : Finset (Fin n)) :
    IsBalance M S (purchase M S) (visitNot M S) ∧
    (∀ j, 0 ≤ purchase M S j) ∧ (∀ j, 0 ≤ visitNot M S j) ∧
    ∀ P R : Fin n → ℝ, IsBalance M S P R → P = purchase M S ∧ R = visitNot M S := by sorry

end MarkovChainChoice.Reduced
