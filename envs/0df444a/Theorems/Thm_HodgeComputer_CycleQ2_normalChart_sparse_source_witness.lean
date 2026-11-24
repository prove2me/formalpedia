-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_sparse_source_witness
-- name    : HodgeComputer.CycleQ2.normalChart_sparse_source_witness
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T22:37:02.6779+00:00
-- url     : https://prove2.me/theorems/feca3e76-ea56-4c69-820b-2e7f349acc7c
-- title:
--   Cycle-q2 normal chart with a two-monomial source
-- statement:
--   Let $F$ be the cyclic sextic and set $B = A/2$. Write
--
--   $$\Delta = -9 X_0^6 X_1^2 X_2^3 Y_0^2 Y_1^2 Y_2 + \tfrac{1}{2} X_0 X_1^2 X_2^6 Y_0^3 Y_1^2 Y_2^2.$$
--
--   `sparseResidue(S, W)` is the normal-chart residue of $(F, B, S, W)$ after the undifferentiated source factor has been replaced by $\Delta$.
--
--   The claim is that there exist a nonzero homogeneous denominator $S$ of degree at least $2$, coprime to $F$, and homogeneous numerator components $W_j$ of degree $\deg S + 7$, together with a polynomial $Q$, such that
--
--   $$\mathrm{sparseResidue}(S, W) = F^2 Q.$$
--
--   The hypotheses are those of the explicit-source witness. The two statements have the same solutions, because $\Delta$ is the two-monomial form of that source factor.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_explicit_source_witness, https://prove2.me/theorems/d92115d2-1e48-404b-91e3-4bdea762dc05. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_sparse_source_witness :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      sparseResidue S W = F ^ 2 * Q := by
  sorry
