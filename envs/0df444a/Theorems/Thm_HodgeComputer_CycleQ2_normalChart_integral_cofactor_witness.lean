-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_integral_cofactor_witness
-- name    : HodgeComputer.CycleQ2.normalChart_integral_cofactor_witness
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T22:52:00.734065+00:00
-- url     : https://prove2.me/theorems/221e8d25-8ee6-41e1-bdb1-778ad8bba90b
-- title:
--   Cycle-q2 normal chart with an integral cofactor
-- statement:
--   Let $F$ be the cyclic sextic and set $B = A/2$. Write $M = X_0 X_1^2 X_2^3 Y_0^2 Y_1^2 Y_2$ and
--
--   $$I = X_2^3 Y_0 Y_2 - 18 X_0^5.$$
--
--   `integralResidue(S, W)` is the normal-chart residue of $(F, B, S, W)$ after the undifferentiated source factor has been replaced by $\tfrac12 M I$.
--
--   The claim is that there exist a nonzero homogeneous denominator $S$ of degree at least $2$, coprime to $F$, and homogeneous numerator components $W_j$ of degree $\deg S + 7$, together with a polynomial $Q$, such that
--
--   $$\mathrm{integralResidue}(S, W) = F^2 Q.$$
--
--   The hypotheses match the factored-source witness. The two equations have the same solutions, because $\tfrac12 I$ is the cofactor $\tfrac12 X_2^3 Y_0 Y_2 - 9 X_0^5$.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_factored_source_witness, https://prove2.me/theorems/b05510bf-69e8-48d8-865e-765723de92d3.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2IntegralCofactor

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_integral_cofactor_witness :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      integralResidue S W = F ^ 2 * Q := by
  sorry
