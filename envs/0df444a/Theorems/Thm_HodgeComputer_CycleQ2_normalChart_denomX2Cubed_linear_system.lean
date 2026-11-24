-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_denomX2Cubed_linear_system
-- name    : HodgeComputer.CycleQ2.normalChart_denomX2Cubed_linear_system
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T18:00:48.064299+00:00
-- url     : https://prove2.me/theorems/41d6ce64-157d-46ef-bb76-5dfa4c2c8c3b
-- statement:
--   Let $F$ be the cyclic sextic, $\Delta$ the two-monomial source, and $\mathtt{denomX2Cubed}=X_2^3$. Equip the ambient ring with sixth-root weights $(2,1,0,3,2,1)$.
--
--   The claim is that there exist homogeneous numerators $W_j$ of degree $10$ in characters $(0,5,2,1,0)$ and a homogeneous quotient $Q$ of degree $10$ and character $1$ such that
--
--   $$\mathrm{chartDivergence}(\mathtt{denomX2Cubed},W)-F^2 Q=-\mathtt{denomX2Cubed}^2\Delta.$$
--
--   This is the named-denominator form of the $S=X_2^3$ graded linear system.
-- source:
--   Named-denominator form of HodgeComputer.CycleQ2.normalChart_X2_cubed_linear_system (Prove2Me 9d61a7a7).

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter
import Definitions.Def_HodgeComputerCycleQ2DenomX2Cubed

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_denomX2Cubed_linear_system :
    ∃ (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      (∀ j, (W j).IsHomogeneous (3 + 7)) ∧
      Q.IsHomogeneous (2 * 3 + 4) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear denomX2Cubed W Q = gradedInhomogeneous denomX2Cubed := by
  sorry
