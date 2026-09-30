-- Prove2me | Theorems.Thm_MarkovChainChoice_Assortment_balance_unique_nonneg
-- name    : MarkovChainChoice.Assortment.balance_unique_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:10:03.480987+00:00
-- url     : https://prove2.me/theorems/af16def9-2012-406f-92cc-cd9cf9594d0f
-- title:
--   The (Balance) equations have a unique, nonnegative solution $(P_S,R_S)$
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model on $N=\{1,\dots,n\}$ with $\lambda_j>0$, $\rho_{j,i}\ge 0$ and $\sum_{i\in N}\rho_{j,i}<1$ for all $j$. Then for every offer set $S\subseteq N$ the (Balance) equations
--
--   $$
--   P_j+R_j=\lambda_j+\sum_{i\in N}\rho_{i,j}R_i\ \ \forall j\in N,\qquad P_j=0\ \ \forall j\notin S,\qquad R_j=0\ \ \forall j\in S
--   $$
--
--   have exactly one solution $(P_S,R_S)$, and it satisfies $P_{j,S}\ge 0$ and $R_{j,S}\ge 0$ for all $j\in N$.
--
--   This is what makes the purchase probabilities $P_{j,S}$ well defined, and every later result is stated in terms of them.
--
--   **Formalization Note.** The statement is about the objects `purchase M S` and `visitNot M S` of the definition layer: they satisfy (Balance), are nonnegative, and coincide with every solution of (Balance).
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1325, Section 2, last sentence of the left column continuing into the right column

import Mathlib
import Definitions.Def_MarkovChainChoice_Assortment_Model

namespace MarkovChainChoice.Assortment

theorem balance_unique_nonneg {n : ℕ} (M : Model n) (S : Finset (Fin n)) :
    IsBalance M S (purchase M S) (visitNot M S) ∧
    (∀ j, 0 ≤ purchase M S j) ∧ (∀ j, 0 ≤ visitNot M S j) ∧
    ∀ P R : Fin n → ℝ, IsBalance M S P R → P = purchase M S ∧ R = visitNot M S := by sorry

end MarkovChainChoice.Assortment
