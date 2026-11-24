-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_chart_divergence_membership
-- name    : HodgeComputer.CycleQ2.normalChart_chart_divergence_membership
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:38:34.881805+00:00
-- url     : https://prove2.me/theorems/ead9e89c-8b71-45cc-80de-348bc740af4d
-- title:
--   Sparse carrier as a chart divergence
-- statement:
--   Let $F$ be the cyclic sextic and set $B = A/2$. Write $\Delta$ for the two-monomial source and $\mathrm{chartDivergence}(S,W)$ for the sum of the five numerator terms in the normal-chart residue. The carrier is
--
--   $$\mathrm{divergenceCarrier}(S,W) = \mathrm{chartDivergence}(S,W) + S^2\Delta.$$
--
--   The claim is that there exist a nonzero homogeneous denominator $S$ of degree at least $2$, coprime to $F$, homogeneous numerator components $W_j$ of degree $\deg S + 7$, and a polynomial $Q$, such that
--
--   $$\mathrm{divergenceCarrier}(S,W) = F^2 Q.$$
--
--   The hypotheses are those of the sparse linear-membership witness. The two carriers have the same solutions: the residue equals $S^2 U$ plus the chart divergence, and removing $S^2 U$ leaves the divergence.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_sparse_linear_membership, https://prove2.me/theorems/e160c92a-a560-4c02-822f-2583a4b40581. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_chart_divergence_membership :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      divergenceCarrier S W = F ^ 2 * Q := by
  sorry
