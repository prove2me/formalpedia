-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_degree_three_X2_cubed
-- name    : HodgeComputer.CycleQ2.normalChart_character_zero_degree_three_X2_cubed
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T14:17:25.468004+00:00
-- url     : https://prove2.me/theorems/26b82810-966d-465a-92ab-8c5860e9dc0c
-- statement:
--   Let $F$ be the cyclic sextic and $\Delta$ the two-monomial source, with sixth-root weights $(2,1,0,3,2,1)$.
--
--   The claim is that there exist homogeneous numerators $W_j$ of degree $10$ in characters $(0,5,2,1,0)$ and a homogeneous quotient $Q$ of degree $10$ and character $1$ such that, for the denominator $S=X_2^3$,
--
--   $$\mathrm{chartDivergence}(S,W)-F^2 Q=-S^2\Delta.$$
--
--   This is the $X_2^3$ stratum of the character-zero degree-three NormalChart existence: $X_2$ has weight $0$, so $\chi(S)=0$, and $S$ is homogeneous of degree $3$.
-- source:
--   Monomial specialization of HodgeComputer.CycleQ2.normalChart_character_zero_degree_three (Prove2Me 127a2775) at S=X_2^3.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_character_zero_degree_three_X2_cubed :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S = (MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ) ∧
      S ≠ 0 ∧ S.IsHomogeneous 3 ∧ S.totalDegree = 3 ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (3 + 7)) ∧
      Q.IsHomogeneous (2 * 3 + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  sorry
