-- Prove2me | Theorems.Thm_MarkovChainChoice_DimReduction_drAlpha_le_one
-- name    : MarkovChainChoice.DimReduction.drAlpha_le_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:06:06.079276+00:00
-- url     : https://prove2.me/theorems/b1341f5f-530d-4e2b-8b33-d6f3a632d8d9
-- title:
--   Section 7 — the step size $\alpha_{\hat x}$ is at most one on $\mathcal H$
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model satisfying the standing assumptions, let $(\hat x,\hat z)\in\mathcal H$, and suppose $S_{\hat x}=\{j\in N:\hat x_j>0\}$ is nonempty. Then
--   $$
--   \alpha_{\hat x}=\min\Big\{\frac{\hat x_j}{P_{j,S_{\hat x}}}: j\in S_{\hat x}\Big\}\ \le\ 1 .
--   $$
--   Hence Step 2 of the Dimension Reduction algorithm either stops ($\alpha=1$) or produces $\alpha<1$, so Step 3 is well defined.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1332, Section 7, right column

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
import Definitions.Def_MarkovChainChoice_Shared_Balance
import Definitions.Def_MarkovChainChoice_DimReduction_H
import Definitions.Def_MarkovChainChoice_DimReduction_Algorithm
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

theorem drAlpha_le_one {n : ℕ} (M : Model n) :
    ∀ p ∈ H M, (drSupp p.1).Nonempty → drAlpha M p.1 ≤ 1 := by sorry

end MarkovChainChoice.DimReduction
