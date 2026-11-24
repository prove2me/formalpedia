-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_degree_three
-- name    : HodgeComputer.CycleQ2.normalChart_character_zero_degree_three
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T13:36:52.184877+00:00
-- url     : https://prove2.me/theorems/127a2775-eb46-4bc2-ba17-a4373cc73077
-- statement:
--   Let $F$ be the cyclic sextic. Write $\Delta$ for the two-monomial source and equip the ambient ring with sixth-root weights $(2,1,0,3,2,1)$.
--
--   The claim is that there exist a nonzero homogeneous denominator $S$ of degree exactly $3$, coprime to $F$, of character $0$, homogeneous numerators $W_j$ of degree $10$ in characters $(0,5,2,1,0)$, and a homogeneous quotient $Q$ of degree $10$ and character $1$, such that
--
--   $$\mathrm{chartDivergence}(S,W)-F^2 Q=-S^2\Delta.$$
--
--   This is the exact-degree-$3$ specialization of the character-zero degree-at-least-three existence. The character-$0$ cubic stratum is spanned by the ten monomials $X_0^3$, $X_0^2 Y_1$, $X_0 X_1 Y_0$, $X_0 Y_0 Y_2$, $X_0 Y_1^2$, $X_1 Y_0 Y_1$, $X_2^3$, $X_2 Y_0^2$, $Y_0 Y_1 Y_2$, $Y_1^3$.
-- source:
--   Specialization of HodgeComputer.CycleQ2.normalChart_character_zero_degree_at_least_three (Prove2Me 4398e664) to exact degree e=3; cyclic sextic NormalChart residue at character 0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_character_zero_degree_three :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous 3 ∧ S.totalDegree = 3 ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (3 + 7)) ∧
      Q.IsHomogeneous (2 * 3 + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  sorry
