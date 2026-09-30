-- Prove2me | Theorems.Thm_MarkovChainChoice_DimReduction_visitNot_le_of_mem_H
-- name    : MarkovChainChoice.DimReduction.visitNot_le_of_mem_H
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:04:56.70499+00:00
-- url     : https://prove2.me/theorems/282f20f7-b418-45b3-b154-e04c59e88d6d
-- title:
--   Lemma 11 (as quoted on p. 1332) — $\hat z_j\ge R_{j,S_{\hat x}}$ on $\mathcal H$
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model satisfying the standing assumptions, and let $(\hat x,\hat z)\in\mathcal H$. Write $S_{\hat x}=\{j\in N:\hat x_j>0\}$. Then
--   $$
--   \hat z_j\ \ge\ R_{j,S_{\hat x}}\qquad\text{for all } j\in N .
--   $$
--   In words, $\hat z$ dominates the visit-count vector of the (Balance) solution for the offer set given by the support of $\hat x$.
--
--   This comparison is the input to the bound $\alpha\le1$ on the step size of the Dimension Reduction algorithm and to the nonnegativity of the updated $z$ in Lemma 8.
--
--   **Formalization Note** The paper proves this as Lemma 11 in its online appendix, which is not reproduced here; the statement is the one quoted in the main text on p. 1332.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1332, Section 7, right column, quoting Lemma 11 of Online Appendix E

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
import Definitions.Def_MarkovChainChoice_Shared_Balance
import Definitions.Def_MarkovChainChoice_DimReduction_H
import Definitions.Def_MarkovChainChoice_DimReduction_Algorithm
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

theorem visitNot_le_of_mem_H {n : ℕ} (M : Model n) :
    ∀ p ∈ H M, ∀ j, visitNot M (drSupp p.1) j ≤ p.2 j := by sorry

end MarkovChainChoice.DimReduction
