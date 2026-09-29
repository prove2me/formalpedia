-- Prove2me | Theorems.Thm_NonmonotoneLS_Global_costQ_le_inv
-- name    : NonmonotoneLS.Global.costQ_le_inv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:28:42.877344+00:00
-- url     : https://prove2.me/theorems/4edadce2-a8e9-4a0f-b9f4-533bec07164b
-- title:
--   Eq. (2.15) — $Q_{k+1} \le 1/(1-\eta_{\max})$
-- statement:
--   Let $0 \le \eta_k \le \eta_{\max}$ for every $k$, where $\eta_{\max} < 1$, and let $Q_0 = 1$, $Q_{k+1} = \eta_k Q_k + 1$ as in (1.6). Then for every $k$
--
--   $$Q_{k+1} \le 1 + \sum_{j=0}^{k} \eta_{\max}^{j+1} \le \frac{1}{1-\eta_{\max}}.$$
--
--   With this uniform bound the series (2.14) controls $\sum_k \|\nabla f(x_k)\|^2$ itself, which gives $\nabla f(x_k) \to 0$ in Theorem 2.2.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1048, Eq. (2.15) (proof of Theorem 2.2)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Eq. (2.15) (p. 1048): if `η_k ∈ [0, η_max]` for all `k` and `η_max < 1`, then
`Q_{k+1} ≤ 1 + ∑_{j=0}^{k} η_max^{j+1} ≤ 1/(1 - η_max)`. -/
theorem costQ_le_inv (η : ℕ → ℝ) (ηmax : ℝ) (hη : ∀ k, η k ∈ Set.Icc (0 : ℝ) ηmax)
    (hηmax : ηmax < 1) (k : ℕ) :
    Shared.costQ η (k + 1) ≤ 1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) ∧
      1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) ≤ 1 / (1 - ηmax) := by sorry

end NonmonotoneLS.Global
