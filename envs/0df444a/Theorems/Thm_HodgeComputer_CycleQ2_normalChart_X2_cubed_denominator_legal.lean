-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_X2_cubed_denominator_legal
-- name    : HodgeComputer.CycleQ2.normalChart_X2_cubed_denominator_legal
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T17:01:25.728959+00:00
-- url     : https://prove2.me/theorems/43f548f9-8510-4e4d-8aa2-205ef06a5494
-- statement:
--   Let $F$ be the cyclic sextic fourfold equation and equip the ambient ring with sixth-root weights $(2,1,0,3,2,1)$.
--
--   The claim is that the monomial $S=X_2^3$ is a legal NormalChart denominator: it is nonzero, homogeneous of degree $3$, of total degree $3$, coprime to $F$, and of character $0$ (since the weight of $X_2$ is $0$).
--
--   This isolates the structural side of the $S=X_2^3$ specialization of the character-zero degree-three residue system.
-- source:
--   Structural half of HodgeComputer.CycleQ2.normalChart_character_zero_degree_three_X2_cubed (Prove2Me 26b82810).

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_X2_cubed_denominator_legal :
    (MvPolynomial.X (R := ℂ) (2 : Fin 6) : AmbientPoly n) ^ (3 : ℕ) ≠ 0 ∧
      ((MvPolynomial.X (R := ℂ) (2 : Fin 6) : AmbientPoly n) ^ (3 : ℕ)).IsHomogeneous 3 ∧
      ((MvPolynomial.X (R := ℂ) (2 : Fin 6) : AmbientPoly n) ^ (3 : ℕ)).totalDegree = 3 ∧
      IsRelPrime F ((MvPolynomial.X (R := ℂ) (2 : Fin 6) : AmbientPoly n) ^ (3 : ℕ)) ∧
      IsCharacter 0 ((MvPolynomial.X (R := ℂ) (2 : Fin 6) : AmbientPoly n) ^ (3 : ℕ) : AmbientPoly 5) := by
  sorry
