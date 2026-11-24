-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_X2_cubed_relPrime
-- name    : HodgeComputer.CycleQ2.normalChart_X2_cubed_relPrime
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T17:50:09.293827+00:00
-- url     : https://prove2.me/theorems/11f1098f-ccc0-4af1-8acd-95e5ff544bc3
-- statement:
--   Let $F$ be the cyclic sextic fourfold equation. The claim is that $F$ is coprime to the monomial $X_2^3$ in the ambient polynomial ring: any common divisor is a unit.
--
--   Since $X_2$ does not divide $F$, powers of $X_2$ remain relatively prime to $F$. This is the coprimality conjunct of the $S=X_2^3$ denominator legality lemma.
-- source:
--   Coprimality half of HodgeComputer.CycleQ2.normalChart_X2_cubed_denominator_legal (Prove2Me 43f548f9).

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_X2_cubed_relPrime :
    IsRelPrime F ((MvPolynomial.X (R := ℂ) (2 : Fin 6) : AmbientPoly n) ^ (3 : ℕ)) := by
  sorry
