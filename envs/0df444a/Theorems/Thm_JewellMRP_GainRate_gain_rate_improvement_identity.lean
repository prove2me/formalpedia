-- Prove2me | Theorems.Thm_JewellMRP_GainRate_gain_rate_improvement_identity
-- name    : JewellMRP.GainRate.gain_rate_improvement_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:25:56.694081+00:00
-- url     : https://prove2.me/theorems/1ad7eef5-8eae-410c-9805-64b865374a7e
-- title:
--   Eq. (D 3): the change in gain rate equals the $P^B$-average of the test-quantity improvements
-- statement:
--   Let a Markov-renewal program be ergodic with positive mean sojourn times. Let $A$ and $B$ be two stationary policies, let $(g^A, v^A)$ solve the value-determination equations (13) of $A$, and let $\pi^A$, $\pi^B$ be stationary probability vectors of the chains of $A$ and $B$. Write $g(A)$, $g(B)$ for the gain rates (B 7) computed from $\pi^A$, $\pi^B$, and $P^B_j = \nu^B_j \pi^B_j / \sum_k \pi^B_k \nu^B_k$ for the time-stationary probabilities (C 12) of $B$. For each state $j$ let
--   $$\Gamma_j = \Big(\rho^B_j + \sum_{l} p^B_{jl} v^A_l - g^A \nu^B_j\Big) - \Big(\rho^A_j + \sum_{l} p^A_{jl} v^A_l - g^A \nu^A_j\Big)$$
--   be the change in Schweitzer's test quantity (D 1), and
--   $$\gamma_j = \frac{1}{\nu^B_j}\Big(\rho^B_j + \sum_{l} p^B_{jl} v^A_l - v^A_j\Big) - \frac{1}{\nu^A_j}\Big(\rho^A_j + \sum_{l} p^A_{jl} v^A_l - v^A_j\Big)$$
--   the change in the test quantity (D 2) of Fig. 2, both computed with the relative values and gain rate of $A$. Then
--   $$g(B) - g(A) = \sum_{j=1}^{N} \frac{\Gamma_j}{\nu^B_j}\, P^B_j \qquad\text{and}\qquad g(B) - g(A) = \sum_{j=1}^{N} \gamma_j\, P^B_j .$$
--
--   This identity is the engine of the convergence argument: when every $\gamma_j \ge 0$ the gain rate cannot decrease, and a strict improvement at a state $j$ with $P^B_j > 0$ increases it strictly.
--
--   **Formalization Note** The paper states (D 3) for a policy $A$ "which led to an improved policy $B$", with $\Gamma_i \ge 0$ and $\gamma_i \ge 0$; the identities hold for any two policies, and are stated here without that restriction.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 970, Eq. (D 3), with (D 1)-(D 2) (pp. 969-970) and (C 12) (p. 969)

import Mathlib
import Definitions.Def_JewellMRP_GainRate_MRP
import Definitions.Def_JewellMRP_GainRate_PolicyIteration

namespace JewellMRP.GainRate
theorem gain_rate_improvement_identity {N : ℕ} [NeZero N] {α : Type*} (M : MRP N α)
    (hM : M.IsErgodic) (zA zB : Fin N → α) (gA : ℝ) (vA : Fin N → ℝ)
    (hA : M.SolvesValueDetermination zA gA vA) (πA πB : Fin N → ℝ)
    (hπA : IsStationaryDist (M.policyMatrix zA) πA)
    (hπB : IsStationaryDist (M.policyMatrix zB) πB) :
    M.gainRate zB πB - M.gainRate zA πA =
        ∑ j, ((M.schweitzerTestQuantity gA vA j (zB j) -
            M.schweitzerTestQuantity gA vA j (zA j)) / M.ν j (zB j)) *
          M.timeStationaryProb zB πB j ∧
      M.gainRate zB πB - M.gainRate zA πA =
        ∑ j, (M.testQuantity vA j (zB j) - M.testQuantity vA j (zA j)) *
          M.timeStationaryProb zB πB j := by sorry
end JewellMRP.GainRate
