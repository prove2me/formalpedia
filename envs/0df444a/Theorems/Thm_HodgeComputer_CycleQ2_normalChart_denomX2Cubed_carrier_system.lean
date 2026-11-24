-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_denomX2Cubed_carrier_system
-- name    : HodgeComputer.CycleQ2.normalChart_denomX2Cubed_carrier_system
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:21:40.430412+00:00
-- url     : https://prove2.me/theorems/8cd02786-f2f3-400c-83ca-2d2c6d5806e3
-- statement:
--   Let $F$ be the cyclic sextic, $\Delta$ the two-monomial source, and $\mathtt{denomX2Cubed}=X_2^3$. Equip the ambient ring with sixth-root weights $(2,1,0,3,2,1)$.
--
--   The claim is that there exist homogeneous numerators $W_j$ of degree $10$ in characters $(0,5,2,1,0)$ and a homogeneous quotient $Q$ of degree $10$ and character $1$ such that
--
--   $$\mathrm{divergenceCarrier}(\mathtt{denomX2Cubed},W)=F^2 Q.$$
--
--   This is the Diamond-style carrier form of the fixed-denominator graded NormalChart linear system.
-- source:
--   Carrier form of HodgeComputer.CycleQ2.normalChart_denomX2Cubed_linear_system (Prove2Me 41d6ce64).

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

theorem HodgeComputer.CycleQ2.normalChart_denomX2Cubed_carrier_system :
    ∃ (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      (∀ j, (W j).IsHomogeneous (3 + 7)) ∧
      Q.IsHomogeneous (2 * 3 + 4) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      divergenceCarrier denomX2Cubed W = (F : AmbientPoly n) ^ 2 * Q := by
  sorry
