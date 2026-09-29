-- Prove2me | Theorems.Thm_NonmonotoneLS_Global_costQ_closed_form
-- name    : NonmonotoneLS.Global.costQ_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:22:24.178591+00:00
-- url     : https://prove2.me/theorems/54333aec-3069-40b8-9fb3-2fe763f74610
-- title:
--   Eq. (1.8) — closed form of $Q_{j+1}$ and $Q_{j+1} \le j+2$
-- statement:
--   Let $\eta_0, \eta_1, \dots$ be real numbers in $[0,1]$ and let $Q_0 = 1$, $Q_{k+1} = \eta_k Q_k + 1$ as in (1.6). Then for every $j \ge 0$
--
--   $$Q_{j+1} = 1 + \sum_{i=0}^{j} \prod_{m=0}^{i} \eta_{j-m} \le j + 2.$$
--
--   The bound $Q_{k+1} \le k+2$ is what gives $C_k \le A_k$ in Lemma 1.1 and what turns the summability (2.14) into $\liminf_k \|\nabla f(x_k)\| = 0$ in Theorem 2.2.
--
--   **Formalization Note.** The index $j - m$ is natural-number subtraction, but $m \le i \le j$ throughout the sum, so it never truncates.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1045, Eq. (1.8) (proof of Lemma 1.1)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Eq. (1.8) (p. 1045): if `η_k ∈ [0, 1]` for all `k`, then
`Q_{j+1} = 1 + ∑_{i=0}^{j} ∏_{m=0}^{i} η_{j-m} ≤ j + 2`. -/
theorem costQ_closed_form (η : ℕ → ℝ) (hη : ∀ k, η k ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    Shared.costQ η (j + 1) =
        1 + ∑ i ∈ Finset.range (j + 1), ∏ m ∈ Finset.range (i + 1), η (j - m) ∧
      Shared.costQ η (j + 1) ≤ (j : ℝ) + 2 := by sorry

end NonmonotoneLS.Global
