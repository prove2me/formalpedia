-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_degree_case_split
-- name    : HodgeComputer.CycleQ2.normalChart_character_zero_degree_case_split
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T01:17:21.306965+00:00
-- url     : https://prove2.me/theorems/1c6a9211-fa79-4c82-a030-57040c803b1d
-- title:
--   Character-zero system: degree $2$ or degree $\ge 3$
-- statement:
--   Let $F$ be the cyclic sextic. Write $\Delta$ for the two-monomial source and equip the ambient ring with sixth-root weights $(2,1,0,3,2,1)$.
--
--   The character-zero weighted-numerator system at an explicit degree splits into two exhaustive strata:
--
--   1. Degree exactly $2$: there exist $S,W,Q$ of the usual characters with $\deg S=2$ such that $\mathrm{chartDivergence}(S,W)-F^2 Q=-S^2\Delta$. In this degree the character-$0$ summands are spanned by $X_2^2$ and $Y_0^2$, so $S$ lies on the pencil $X_2^2 + t Y_0^2$ up to scale.
--
--   2. Degree at least $3$: the same system for some $e\ge 3$.
--
--   Either disjunct yields a solution of the parameterized existence statement with $2\le e$.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_character_zero_weighted_numerators_at_degree, https://prove2.me/theorems/0cdf2da2-2b63-4982-a800-bd09e6c89c46. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_character_zero_degree_case_split :
    (∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous 2 ∧ S.totalDegree = 2 ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (2 + 7)) ∧
      Q.IsHomogeneous (2 * 2 + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S) ∨
    (∃ (e : ℕ) (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      3 ≤ e ∧
      S ≠ 0 ∧ S.IsHomogeneous e ∧ S.totalDegree = e ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (e + 7)) ∧
      Q.IsHomogeneous (2 * e + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S) := by
  sorry
