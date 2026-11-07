-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalDerivative_relPrime
-- name    : HodgeComputer.CycleQ2.normalDerivative_relPrime
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T03:44:02.572205+00:00
-- url     : https://prove2.me/theorems/f41a25e5-5805-4433-a2c9-ea676f4a4b2a
-- title:
--   Cycle q2: the first normal derivative is a legal denominator
-- statement:
--   For exactly the sextic $F$ of the cycle-q2 instance, its first partial derivative is relatively prime to $F$:
--
--   $$\operatorname{IsRelPrime}_{\mathbb C[X_0,X_1,X_2,Y_0,Y_1,Y_2]}\left(F,\frac{\partial F}{\partial X_0}\right).$$
--
--   Every common polynomial divisor is therefore a unit. This is the denominator-admissibility condition for the normal-chart certificate construction. The assertion concerns polynomial relative primality, not comaximality.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/cycle-q2/instance.rec; derived exact coprimality consequence, proved by line specialization.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalDerivative_relPrime :
    IsRelPrime F (NormalChart.normal F) := by sorry
