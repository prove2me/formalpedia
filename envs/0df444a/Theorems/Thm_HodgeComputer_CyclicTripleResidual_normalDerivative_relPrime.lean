-- Prove2me | Theorems.Thm_HodgeComputer_CyclicTripleResidual_normalDerivative_relPrime
-- name    : HodgeComputer.CyclicTripleResidual.normalDerivative_relPrime
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T03:44:20.283718+00:00
-- url     : https://prove2.me/theorems/fe381b0b-0c3b-4b02-a5b9-8c13e83440f7
-- title:
--   Cyclic triple residual: the first normal derivative is a legal denominator
-- statement:
--   For exactly the sextic $F$ of the cyclic-triple-residual instance, its first partial derivative is relatively prime to $F$:
--
--   $$\operatorname{IsRelPrime}_{\mathbb C[X_0,X_1,X_2,Y_0,Y_1,Y_2]}\left(F,\frac{\partial F}{\partial X_0}\right).$$
--
--   Every common polynomial divisor is therefore a unit. This is the denominator-admissibility condition for the normal-chart certificate construction. The assertion concerns polynomial relative primality, not comaximality.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/cyclic-triple-residual/instance.rec; derived exact coprimality consequence, proved by line specialization.

import Definitions.Def_HodgeComputerCyclicTripleResidual
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.CyclicTripleResidual

theorem HodgeComputer.CyclicTripleResidual.normalDerivative_relPrime :
    IsRelPrime F (NormalChart.normal F) := by sorry
