-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_graded_linear_system
-- name    : HodgeComputer.CycleQ2.normalChart_graded_linear_system
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:55:56.340619+00:00
-- url     : https://prove2.me/theorems/0582016f-408c-4e7a-90fd-8ea1ed63a4a8
-- title:
--   Graded linear system for the chart divergence
-- statement:
--   Let $F$ be the cyclic sextic and set $B = A/2$. Write $\Delta$ for the two-monomial source. The graded linear system asks for a nonzero homogeneous denominator $S$ of degree at least $2$, coprime to $F$, homogeneous numerators $W_j$ of degree $\deg S + 7$, and a homogeneous quotient $Q$ of degree $2\deg S + 4$, such that
--
--   $$\mathrm{chartDivergence}(S,W) - F^2 Q = -S^2\Delta.$$
--
--   The hypotheses are those of the homogeneous-quotient membership. The two equations are equivalent by rearranging the sum $\mathrm{chartDivergence}(S,W) + S^2\Delta = F^2 Q$.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_homogeneous_quotient_membership, https://prove2.me/theorems/e1b484fe-a669-4584-8d96-580dd070803a. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_graded_linear_system :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      Q.IsHomogeneous (2 * S.totalDegree + 4) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  sorry
