-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_degree_at_least_three
-- name    : HodgeComputer.CycleQ2.normalChart_character_zero_degree_at_least_three
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T01:26:02.994953+00:00
-- url     : https://prove2.me/theorems/4398e664-eecd-4664-8d8b-40e86cf90547
-- title:
--   Character-zero weighted system in degree $\ge 3$
-- statement:
--   Let $F$ be the cyclic sextic. Write $\Delta$ for the two-monomial source and equip the ambient ring with sixth-root weights $(2,1,0,3,2,1)$.
--
--   The claim is that there exist an integer $e\ge 3$, a nonzero homogeneous denominator $S$ of degree exactly $e$, coprime to $F$, of character $0$, homogeneous numerators $W_j$ of degree $e+7$ in characters $(0,5,2,1,0)$, and a homogeneous quotient $Q$ of degree $2e+4$ and character $1$, such that
--
--   $$\mathrm{chartDivergence}(S,W)-F^2 Q=-S^2\Delta.$$
--
--   This is the higher-degree disjunct of the character-zero degree case split. The degree-$2$ character-$0$ stratum is the pencil spanned by $X_2^2$ and $Y_0^2$; this statement searches in degrees at least $3$.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_character_zero_degree_case_split, https://prove2.me/theorems/1c6a9211-fa79-4c82-a030-57040c803b1d. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_character_zero_degree_at_least_three :
    ∃ (e : ℕ) (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      3 ≤ e ∧
      S ≠ 0 ∧ S.IsHomogeneous e ∧ S.totalDegree = e ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (e + 7)) ∧
      Q.IsHomogeneous (2 * e + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  sorry
