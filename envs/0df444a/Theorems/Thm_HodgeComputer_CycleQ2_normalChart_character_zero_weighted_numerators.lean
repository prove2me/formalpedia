-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_weighted_numerators
-- name    : HodgeComputer.CycleQ2.normalChart_character_zero_weighted_numerators
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T00:21:13.700735+00:00
-- url     : https://prove2.me/theorems/cd0e702e-90b6-4690-b91e-916b938e42ba
-- title:
--   Character-zero system with weighted numerators
-- statement:
--   Let $F$ be the cyclic sextic. Write $\Delta$ for the two-monomial source. Equip the ambient ring with sixth-root weights $(2,1,0,3,2,1)$.
--
--   The claim is that there exist a nonzero homogeneous denominator $S$ of degree at least $2$, coprime to $F$, of character $0$, homogeneous numerators $W_j$ of degree $\deg S+7$ with
--
--   $$W_j\text{ of character }5+\mathrm{sixthRootWeight}(j+1)\pmod{6},$$
--
--   and a homogeneous quotient $Q$ of degree $2\deg S+4$ and character $1$, such that
--
--   $$\mathrm{chartDivergence}(S,W)-F^2 Q=-S^2\Delta.$$
--
--   The hypotheses are those of the character-zero linear system, with each numerator pinned to the character that feeds the character-$1$ summand of the chart divergence. Explicitly the five numerator characters are $(0,5,2,1,0)$.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_character_zero_linear_system, https://prove2.me/theorems/75f1477a-2df3-4a0d-bd43-85d9e80c9fd2. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_character_zero_weighted_numerators :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      Q.IsHomogeneous (2 * S.totalDegree + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  sorry
