-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_weighted_numerators_at_degree
-- name    : HodgeComputer.CycleQ2.normalChart_character_zero_weighted_numerators_at_degree
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T00:29:58.762943+00:00
-- url     : https://prove2.me/theorems/0cdf2da2-2b63-4982-a800-bd09e6c89c46
-- title:
--   Character-zero weighted numerators at an explicit degree
-- statement:
--   Let $F$ be the cyclic sextic. Write $\Delta$ for the two-monomial source and equip the ambient ring with sixth-root weights $(2,1,0,3,2,1)$.
--
--   The claim is that there exist an integer $e\ge 2$, a nonzero homogeneous denominator $S$ of degree exactly $e$, coprime to $F$, of character $0$, homogeneous numerators $W_j$ of degree $e+7$ in characters $(0,5,2,1,0)$, and a homogeneous quotient $Q$ of degree $2e+4$ and character $1$, such that
--
--   $$\mathrm{chartDivergence}(S,W)-F^2 Q=-S^2\Delta.$$
--
--   This is the character-zero weighted-numerator system with the degree written as an explicit search parameter $e$, matching the outer loop of the modular linear-algebra sweep.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_character_zero_weighted_numerators, https://prove2.me/theorems/cd0e702e-90b6-4690-b91e-916b938e42ba. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_character_zero_weighted_numerators_at_degree :
    ∃ (e : ℕ) (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      2 ≤ e ∧
      S ≠ 0 ∧ S.IsHomogeneous e ∧ S.totalDegree = e ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (e + 7)) ∧
      Q.IsHomogeneous (2 * e + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  sorry
