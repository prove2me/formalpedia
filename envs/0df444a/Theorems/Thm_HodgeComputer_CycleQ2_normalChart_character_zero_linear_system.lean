-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_linear_system
-- name    : HodgeComputer.CycleQ2.normalChart_character_zero_linear_system
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T00:07:49.78407+00:00
-- url     : https://prove2.me/theorems/75f1477a-2df3-4a0d-bd43-85d9e80c9fd2
-- title:
--   Graded linear system in character $0$
-- statement:
--   Let $F$ be the cyclic sextic. Write $\Delta$ for the two-monomial source and equip the ambient ring with the sixth-root weights $(2,1,0,3,2,1)$.
--
--   The claim is that there exist a nonzero homogeneous denominator $S$ of degree at least $2$, coprime to $F$, of character $0$, homogeneous numerators $W_j$ of degree $\deg S+7$, and a homogeneous quotient $Q$ of degree $2\deg S+4$ and character $1$, such that
--
--   $$\mathrm{chartDivergence}(S,W) - F^2 Q = -S^2\Delta.$$
--
--   This is the character-linear system specialized to $\chi = 0$. Then $2\chi+1 = 1$, so the quotient character is $1$. Character $0$ is the weight cut used by the modular rank samples.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_character_linear_system, https://prove2.me/theorems/7405ae1e-4da6-44d0-9df9-da4a7b87f553. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_character_zero_linear_system :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      Q.IsHomogeneous (2 * S.totalDegree + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  sorry
