-- Prove2me | Theorems.Thm_MarkovChainChoice_DimReduction_eq_balance_of_supp_empty
-- name    : MarkovChainChoice.DimReduction.eq_balance_of_supp_empty
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:06:49.216991+00:00
-- url     : https://prove2.me/theorems/b314905c-1be5-4667-a0a8-66ea032406d3
-- title:
--   Section 7, first case — a point of $\mathcal H$ with $S_{\hat x}=\emptyset$ equals $(P_\emptyset,R_\emptyset)$
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model satisfying the standing assumptions and let $(\hat x,\hat z)\in\mathcal H$. If $S_{\hat x}=\{j\in N:\hat x_j>0\}=\emptyset$, then
--   $$
--   (\hat x,\hat z)=(P_\emptyset,R_\emptyset),
--   $$
--   the solution of the (Balance) equations for the empty offer set.
--
--   This is the configuration in which the Dimension Reduction algorithm stops in Step 1.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1332, Section 7, right column (first case)

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
import Definitions.Def_MarkovChainChoice_Shared_Balance
import Definitions.Def_MarkovChainChoice_DimReduction_H
import Definitions.Def_MarkovChainChoice_DimReduction_Algorithm
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

theorem eq_balance_of_supp_empty {n : ℕ} (M : Model n) :
    ∀ p ∈ H M, drSupp p.1 = ∅ → p = (purchase M ∅, visitNot M ∅) := by sorry

end MarkovChainChoice.DimReduction
