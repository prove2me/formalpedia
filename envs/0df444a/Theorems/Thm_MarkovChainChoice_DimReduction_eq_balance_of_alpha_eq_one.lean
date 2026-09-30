-- Prove2me | Theorems.Thm_MarkovChainChoice_DimReduction_eq_balance_of_alpha_eq_one
-- name    : MarkovChainChoice.DimReduction.eq_balance_of_alpha_eq_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:07:19.07518+00:00
-- url     : https://prove2.me/theorems/27002a19-bf21-4b5d-9580-7208315b189c
-- title:
--   Section 7, second case — a point of $\mathcal H$ with $\alpha_{\hat x}=1$ equals $(P_{S_{\hat x}},R_{S_{\hat x}})$
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model satisfying the standing assumptions and let $(\hat x,\hat z)\in\mathcal H$ with $S_{\hat x}=\{j\in N:\hat x_j>0\}$ nonempty. If
--   $$
--   \alpha_{\hat x}=\min\Big\{\frac{\hat x_j}{P_{j,S_{\hat x}}}: j\in S_{\hat x}\Big\}=1,
--   $$
--   then $\hat x=P_{S_{\hat x}}$ and $\hat z=R_{S_{\hat x}}$.
--
--   This is the configuration in which the Dimension Reduction algorithm stops in Step 2.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1332, Section 7, right column (second case)

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
import Definitions.Def_MarkovChainChoice_Shared_Balance
import Definitions.Def_MarkovChainChoice_DimReduction_H
import Definitions.Def_MarkovChainChoice_DimReduction_Algorithm
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

theorem eq_balance_of_alpha_eq_one {n : ℕ} (M : Model n) :
    ∀ p ∈ H M, (drSupp p.1).Nonempty → drAlpha M p.1 = 1 →
      p = (purchase M (drSupp p.1), visitNot M (drSupp p.1)) := by sorry

end MarkovChainChoice.DimReduction
