-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_sparse_linear_membership
-- name    : HodgeComputer.CycleQ2.normalChart_sparse_linear_membership
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:30:24.520799+00:00
-- url     : https://prove2.me/theorems/e160c92a-a560-4c02-822f-2583a4b40581
-- title:
--   Sparse residue as membership in the linear carrier
-- statement:
--   Let $F$ be the cyclic sextic and set $B = A/2$. Write $\Delta$ for the two-monomial source and $\mathrm{sparseLinear}(S,W)$ for the normal-chart residue of $(F,B,S,W)$ with the undifferentiated source term removed. The carrier is
--
--   $$\mathrm{sparseCarrier}(S,W) = \mathrm{sparseLinear}(S,W) + S^2\Delta.$$
--
--   The claim is that there exist a nonzero homogeneous denominator $S$ of degree at least $2$, coprime to $F$, homogeneous numerator components $W_j$ of degree $\deg S + 7$, and a polynomial $Q$, such that
--
--   $$\mathrm{sparseCarrier}(S,W) = F^2 Q.$$
--
--   The hypotheses are those of the sparse-source witness. For a fixed $S$, the first summand is linear in $W$, so the equation asks that $F^2 Q - S^2\Delta$ lie in the image of that linear map.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_sparse_source_witness, https://prove2.me/theorems/feca3e76-ea56-4c69-820b-2e7f349acc7c. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2SparseLinear

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_sparse_linear_membership :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      sparseCarrier S W = F ^ 2 * Q := by
  sorry
