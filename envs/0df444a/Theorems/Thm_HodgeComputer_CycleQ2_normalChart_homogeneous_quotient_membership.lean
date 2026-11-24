-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_homogeneous_quotient_membership
-- name    : HodgeComputer.CycleQ2.normalChart_homogeneous_quotient_membership
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:47:54.638464+00:00
-- url     : https://prove2.me/theorems/e1b484fe-a669-4584-8d96-580dd070803a
-- title:
--   Divergence carrier with a homogeneous quotient of degree $2e+4$
-- statement:
--   Let $F$ be the cyclic sextic and set $B = A/2$. Write $\Delta$ for the two-monomial source and $\mathrm{chartDivergence}(S,W)$ for the sum of the five numerator terms. The carrier is
--
--   $$\mathrm{divergenceCarrier}(S,W) = \mathrm{chartDivergence}(S,W) + S^2\Delta.$$
--
--   When $S$ is homogeneous of degree $e$ and each $W_j$ is homogeneous of degree $e+7$, the carrier is homogeneous of degree $2e+16$. Since $F^2$ has degree $12$, any quotient $Q$ satisfying $\mathrm{divergenceCarrier}(S,W) = F^2 Q$ is homogeneous of degree $2e+4$.
--
--   The claim is that there exist a nonzero homogeneous denominator $S$ of degree at least $2$, coprime to $F$, homogeneous numerator components $W_j$ of degree $\deg S + 7$, and a homogeneous quotient $Q$ of degree $2\deg S + 4$, such that
--
--   $$\mathrm{divergenceCarrier}(S,W) = F^2 Q.$$
--
--   The hypotheses are those of the chart-divergence membership, with the degree of $Q$ pinned to the graded piece that the residue occupies.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_chart_divergence_membership, https://prove2.me/theorems/ead9e89c-8b71-45cc-80de-348bc740af4d. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_homogeneous_quotient_membership :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      Q.IsHomogeneous (2 * S.totalDegree + 4) ∧
      divergenceCarrier S W = F ^ 2 * Q := by
  sorry
