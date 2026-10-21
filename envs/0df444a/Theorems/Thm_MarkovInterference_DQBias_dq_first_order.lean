-- Prove2me | Theorems.Thm_MarkovInterference_DQBias_dq_first_order
-- name    : MarkovInterference.DQBias.dq_first_order
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:50.941776+00:00
-- url     : https://prove2.me/theorems/7c84b549-2597-4c64-aab8-61b5e1ff8fe3
-- title:
--   §3.3 — idealized DQ equals the first-order ATE truncation
-- statement:
--   In the finite two-action experiment, let $\rho_{1/2}$ be stationary for the primitive matrix $P_{1/2}$, and put $G=(I-P_{1/2})^\#$. The population differences-in-Q value is
--
--   $$D=\rho_{1/2}^{\top}\bigl(r_1-r_0+(P_1-P_0)G r_{1/2}\bigr).$$
--
--   Whenever $P_0=P_{1/2}-\delta A$ and $P_1=P_{1/2}+\delta A$, this also reads
--
--   $$D=\rho_{1/2}^{\top}r_1-\rho_{1/2}^{\top}r_0+\delta\,\rho_{1/2}^{\top}AG(r_1+r_0).$$
--
--   Thus the idealized estimator matches the constant and linear terms of the expansion of the average treatment effect.
--
--   **Formalization Note** The first displayed formula is stated for the given MDP; the second is universally quantified over perturbation matrices $A$ and scalars $\delta$ satisfying the two matrix identities.
-- source:
--   Farias, Li, Peng, Zheng, Markovian Interference in Experiments, arXiv:2206.02371v2, p. 15, §3.3, the displayed DQ identities after Eq. (6)

import Mathlib
import Definitions.Def_MarkovInterference_DQBias_Chain
import Definitions.Def_MarkovInterference_DQBias_MDP

namespace MarkovInterference.DQBias

/-- §3.3, p. 15: the DQ mean equals the first-order Taylor truncation. -/
theorem dq_first_order {S : Type} [Fintype S] [DecidableEq S]
    (M : MDP S) (rho : S → ℝ)
    (hp : IsPrimitive M.Phalf) (hrho : IsStationaryDist M.Phalf rho) :
    M.dqMean rho = rho ⬝ᵥ
      (M.rvec 1 - M.rvec 0 +
        (M.P 1 - M.P 0).mulVec ((groupInv M.Phalf rho).mulVec M.rHalf)) ∧
    ∀ (A : Matrix S S ℝ) (δ : ℝ),
      M.P 0 = M.Phalf - δ • A → M.P 1 = M.Phalf + δ • A →
      M.dqMean rho = rho ⬝ᵥ M.rvec 1 - rho ⬝ᵥ M.rvec 0 +
        δ * (Matrix.vecMul rho (A * groupInv M.Phalf rho) ⬝ᵥ
          (M.rvec 1 + M.rvec 0)) := by sorry

end MarkovInterference.DQBias
