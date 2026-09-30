-- Prove2me | Theorems.Thm_MarkovChainChoice_SingleResource_balance_unique_nonneg
-- name    : MarkovChainChoice.SingleResource.balance_unique_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:16:05.623791+00:00
-- url     : https://prove2.me/theorems/7ce3682d-ee93-484f-b421-557d31b3c922
-- title:
--   The (Balance) equations have a unique nonnegative solution $(P_S, R_S)$
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model with $\lambda_j>0$, $\rho_{j,i}\ge0$ and $\sum_{i\in N}\rho_{j,i}<1$ for all $j\in N$, and let $S\subseteq N$ be any offer set. Then the (Balance) equations
--   $$P_{j} + R_{j} = \lambda_j + \sum_{i\in N}\rho_{i,j}R_{i}\ \ \forall j\in N,\qquad P_{j}=0\ \ \forall j\notin S,\qquad R_{j}=0\ \ \forall j\in S$$
--   have exactly one solution $(P,R)$, and this solution is nonnegative. In particular the pair $(P_S,R_S)$ used throughout the paper is well defined, and $P_{j,S}\ge 0$, $R_{j,S}\ge0$.
--
--   This is what makes the purchase probabilities $P_{j,S}$ meaningful objects in the assortment problem and the dynamic program.
--
--   **Formalization Note** $(P_S,R_S)$ is the pair `(purchase M S, visitNot M S)` chosen by `Classical.epsilon`; the theorem states that it solves (Balance), that both vectors are nonnegative, and that every solution of (Balance) equals it.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1325, Section 2, last sentence of the left column continuing into the right column

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Balance
open MarkovChainChoice.Shared

namespace MarkovChainChoice.SingleResource

theorem balance_unique_nonneg {n : ℕ} (M : Model n) (S : Finset (Fin n)) :
    IsBalance M S (purchase M S) (visitNot M S) ∧
      (∀ j, 0 ≤ purchase M S j) ∧ (∀ j, 0 ≤ visitNot M S j) ∧
      ∀ P R : Fin n → ℝ, IsBalance M S P R → P = purchase M S ∧ R = visitNot M S := by sorry

end MarkovChainChoice.SingleResource
