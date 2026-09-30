-- Prove2me | Theorems.Thm_MarkovChainChoice_DimReduction_purchase_pos
-- name    : MarkovChainChoice.DimReduction.purchase_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T09:57:35.725995+00:00
-- url     : https://prove2.me/theorems/011dc321-edbf-43a7-b7b3-6be3ba4b1efe
-- title:
--   Section 2 — purchase probabilities are strictly positive on the offer set
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model satisfying the standing assumptions ($\lambda_j>0$, $\rho_{j,i}\ge0$, $\sum_i\rho_{j,i}<1$). For every offer set $S\subseteq N$,
--   $$
--   P_{j,S}>0\qquad\text{for all } j\in S .
--   $$
--   That is, each offered product is purchased with strictly positive probability.
--
--   In the Dimension Reduction algorithm this is what makes the ratios $x_j/P_{j,S}$ of Step 2 meaningful.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1325, Section 2, left column

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
import Definitions.Def_MarkovChainChoice_Shared_Balance
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

theorem purchase_pos {n : ℕ} (M : Model n) (S : Finset (Fin n)) :
    ∀ j ∈ S, 0 < purchase M S j := by sorry

end MarkovChainChoice.DimReduction
