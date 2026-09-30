-- Prove2me | Theorems.Thm_JewellMRP_GainRate_two_state_gain_rate
-- name    : JewellMRP.GainRate.two_state_gain_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:27:09.709486+00:00
-- url     : https://prove2.me/theorems/3c9155b3-285c-431c-a682-21b90d75fa81
-- title:
--   Eqs. (29)-(30): gain rate and relative values of a two-state Markov-renewal process
-- statement:
--   Consider a Markov-renewal program with two states and a stationary policy $z$ whose chain is
--   $$P = \begin{pmatrix} 1 - p_{12} & p_{12} \\ p_{21} & 1 - p_{21} \end{pmatrix}, \qquad p_{12} > 0,\ p_{21} > 0,$$
--   with mean sojourn times $\nu_1, \nu_2 > 0$ and expected rewards $\rho_1, \rho_2$. Let
--   $$g = \frac{p_{21}\rho_1 + p_{12}\rho_2}{\nu_1 p_{21} + \nu_2 p_{12}}, \qquad v_1 = \frac{\nu_2\rho_1 - \nu_1\rho_2}{\nu_1 p_{21} + \nu_2 p_{12}}, \qquad v_2 = 0 .$$
--   Then $(g, v_1, v_2)$ solves the value-determination equations (13) of $z$, and $g$ equals the gain rate (B 7) of $z$ computed from any stationary probability vector of $P$.
--
--   These closed forms let the optimal policy of a two-state program be found by direct evaluation, and they give an explicit, nonvacuous instance of the objects of the algorithm of Fig. 2.
--
--   **Formalization Note** States $1, 2$ are indices $0, 1$ of `Fin 2`. The hypotheses $p_{12}, p_{21} > 0$ make the chain ergodic, as the paper notes below (21); no ergodicity of other policies is assumed.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 961, Eqs. (29)-(30), with (21) (p. 960)

import Mathlib
import Definitions.Def_JewellMRP_GainRate_MRP
import Definitions.Def_JewellMRP_GainRate_PolicyIteration

namespace JewellMRP.GainRate
theorem two_state_gain_rate {α : Type*} (M : MRP 2 α) (z : Fin 2 → α)
    (h12 : 0 < M.p 0 (z 0) 1) (h21 : 0 < M.p 1 (z 1) 0) :
    let p12 := M.p 0 (z 0) 1
    let p21 := M.p 1 (z 1) 0
    let ν1 := M.ν 0 (z 0)
    let ν2 := M.ν 1 (z 1)
    let ρ1 := M.ρ 0 (z 0)
    let ρ2 := M.ρ 1 (z 1)
    let g := (p21 * ρ1 + p12 * ρ2) / (ν1 * p21 + ν2 * p12)
    M.SolvesValueDetermination z g ![(ν2 * ρ1 - ν1 * ρ2) / (ν1 * p21 + ν2 * p12), 0] ∧
      ∀ π : Fin 2 → ℝ, IsStationaryDist (M.policyMatrix z) π → M.gainRate z π = g := by sorry
end JewellMRP.GainRate
