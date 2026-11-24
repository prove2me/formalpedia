-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_factored_source_witness
-- name    : HodgeComputer.CycleQ2.normalChart_factored_source_witness
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T22:44:06.824685+00:00
-- url     : https://prove2.me/theorems/b05510bf-69e8-48d8-865e-765723de92d3
-- title:
--   Cycle-q2 normal chart with a factored source
-- statement:
--   Let $F$ be the cyclic sextic and set $B = A/2$. Factor the source as $M \cdot L$ with
--
--   $$M = X_0 X_1^2 X_2^3 Y_0^2 Y_1^2 Y_2, \qquad L = \tfrac12 X_2^3 Y_0 Y_2 - 9 X_0^5.$$
--
--   `factoredResidue(S, W)` is the normal-chart residue of $(F, B, S, W)$ after the undifferentiated source factor has been replaced by $M \cdot L$.
--
--   The claim is that there exist a nonzero homogeneous denominator $S$ of degree at least $2$, coprime to $F$, and homogeneous numerator components $W_j$ of degree $\deg S + 7$, together with a polynomial $Q$, such that
--
--   $$\mathrm{factoredResidue}(S, W) = F^2 Q.$$
--
--   The hypotheses match the explicit-source witness. The two equations have the same solutions, because $M \cdot L$ is that source factor.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_explicit_source_witness, https://prove2.me/theorems/d92115d2-1e48-404b-91e3-4bdea762dc05.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2FactoredSource

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_factored_source_witness :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      factoredResidue S W = F ^ 2 * Q := by
  sorry
