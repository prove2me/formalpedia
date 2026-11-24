-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_X2_cubed_linear_system
-- name    : HodgeComputer.CycleQ2.normalChart_X2_cubed_linear_system
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T17:01:26.747627+00:00
-- url     : https://prove2.me/theorems/9d61a7a7-7131-42df-99dc-7b9dc57a83d2
-- statement:
--   Let $F$ be the cyclic sextic, $\Delta$ the two-monomial source, and $S=X_2^3$. Equip the ambient ring with sixth-root weights $(2,1,0,3,2,1)$.
--
--   The claim is that there exist homogeneous numerators $W_j$ of degree $10$ in characters $(0,5,2,1,0)$ and a homogeneous quotient $Q$ of degree $10$ and character $1$ such that
--
--   $$\mathrm{chartDivergence}(S,W)-F^2 Q=-S^2\Delta.$$
--
--   This is the graded linear-algebra core of the $S=X_2^3$ NormalChart specialization.
-- source:
--   Linear-algebra half of HodgeComputer.CycleQ2.normalChart_character_zero_degree_three_X2_cubed (Prove2Me 26b82810).

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_X2_cubed_linear_system :
    ∃ (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      (∀ j, (W j).IsHomogeneous (3 + 7)) ∧
      Q.IsHomogeneous (2 * 3 + 4) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ)) W Q =
        gradedInhomogeneous ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ)) := by
  sorry
