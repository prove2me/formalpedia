-- Prove2me | Theorems.Thm_NonmonotoneLS_RLinear_costQ_le_inv
-- name    : NonmonotoneLS.RLinear.costQ_le_inv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:33:03.024992+00:00
-- url     : https://prove2.me/theorems/19a823b5-772e-4fd0-b35b-80025fe041bd
-- title:
--   Eq. (2.15) — $Q_{k+1} \le 1/(1-\eta_{\max})$
-- statement:
--   Let $\eta_0, \eta_1, \dots$ be weights with $0 \le \eta_k \le \eta_{\max}$ for all $k$, where $\eta_{\max} < 1$, and let $Q_k$ be defined by $Q_0 = 1$, $Q_{k+1} = \eta_k Q_k + 1$ (1.6). Then for every $k$
--
--   $$Q_{k+1} \le 1 + \sum_{j=0}^{k} \eta_{\max}^{j+1} \le \frac{1}{1 - \eta_{\max}}. \quad (2.15)$$
--
--   The uniform bound on $Q_{k+1}$ is what turns the per-step decrease $\beta\|g_k\|^2/Q_{k+1}$ of $C_k$ into a decrease proportional to $1 - \eta_{\max}$.
--
--   **Formalization Note.** Both inequalities of the printed chain are stated; the equality in the chain is the closed form (1.8).
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1048, Eq. (2.15)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants

open scoped InnerProductSpace NNReal
open Filter

namespace NonmonotoneLS.RLinear

/-- Eq. (2.15) (p. 1048): if `η_k ∈ [0, η_max]` for all `k` and `η_max < 1`, then
`Q_{k+1} ≤ 1 + ∑_{j=0}^{k} η_max^{j+1} ≤ 1/(1 - η_max)`. -/
theorem costQ_le_inv (η : ℕ → ℝ) (ηmax : ℝ) (hη : ∀ k, η k ∈ Set.Icc (0 : ℝ) ηmax)
    (hηmax : ηmax < 1) (k : ℕ) :
    Shared.costQ η (k + 1) ≤ 1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) ∧
      1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) ≤ 1 / (1 - ηmax) := by sorry

end NonmonotoneLS.RLinear
