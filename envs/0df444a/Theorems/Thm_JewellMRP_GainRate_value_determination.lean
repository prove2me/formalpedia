-- Prove2me | Theorems.Thm_JewellMRP_GainRate_value_determination
-- name    : JewellMRP.GainRate.value_determination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:25:25.805725+00:00
-- url     : https://prove2.me/theorems/8325dbac-b7ff-4931-a213-a0366964dabb
-- title:
--   Eqs. (12)-(13): the value-determination equations have a unique solution with $v_N = 0$, and its $g$ is the gain rate (B 7)
-- statement:
--   Let a Markov-renewal program with $N \ge 1$ states be ergodic, i.e. the transition matrix of every stationary policy is irreducible, and let every mean sojourn time $\nu^z_i$ be positive. Fix a stationary policy $z$ and write $p_{ij}$, $\nu_i$, $\rho_i$ for its data. Then:
--
--   1. the equations (13)
--   $$v_i + g\,\nu_i = \rho_i + \sum_{j=1}^{N} p_{ij} v_j \quad (i = 1, \dots, N), \qquad v_N = 0,$$
--   in the $N + 1$ unknowns $g, v_1, \dots, v_N$ have exactly one solution $(g, v)$;
--   2. for every solution $(g, v)$ and every stationary probability vector $\pi$ of the chain $P = (p_{ij})$,
--   $$g = \frac{\sum_{i} \pi_i \rho_i}{\sum_k \pi_k \nu_k},$$
--   the gain rate (B 7) of $z$.
--
--   This is the value-determination step of the algorithm of Fig. 2: it justifies calling the $g$ produced by (13) the gain rate of the current policy, and the $v_i$ its relative values.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 955, Eqs. (12)-(13); p. 954, Eq. (B 7)

import Mathlib
import Definitions.Def_JewellMRP_GainRate_MRP
import Definitions.Def_JewellMRP_GainRate_PolicyIteration

namespace JewellMRP.GainRate
theorem value_determination {N : ℕ} [NeZero N] {α : Type*} (M : MRP N α)
    (hM : M.IsErgodic) (z : Fin N → α) :
    (∃! gv : ℝ × (Fin N → ℝ), M.SolvesValueDetermination z gv.1 gv.2) ∧
      ∀ (g : ℝ) (v π : Fin N → ℝ), M.SolvesValueDetermination z g v →
        IsStationaryDist (M.policyMatrix z) π → g = M.gainRate z π := by sorry
end JewellMRP.GainRate
