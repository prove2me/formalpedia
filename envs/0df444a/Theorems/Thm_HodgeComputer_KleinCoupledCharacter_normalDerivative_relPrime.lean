-- Prove2me | Theorems.Thm_HodgeComputer_KleinCoupledCharacter_normalDerivative_relPrime
-- name    : HodgeComputer.KleinCoupledCharacter.normalDerivative_relPrime
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T03:48:19.630594+00:00
-- url     : https://prove2.me/theorems/91ece9d7-ab7a-43a2-be09-c4ba26dcc0c0
-- title:
--   Coupled Klein: the first normal derivative is a legal denominator
-- statement:
--   For exactly the coupled Klein sextic $F$, every common divisor of $F$ and $\partial F/\partial X_0$ in $\mathbb C[X_0,X_1,X_2,Y_0,Y_1,Y_2]$ is a unit. Thus the first normal derivative satisfies the polynomial coprimality condition required of a certificate denominator. The assertion is `IsRelPrime`, rather than comaximality.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/klein-coupled-character/instance.rec; derived normal-derivative coprimality verified using a different main coordinate.

import Definitions.Def_HodgeComputerKleinCoupledCharacter
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.KleinCoupledCharacter

theorem HodgeComputer.KleinCoupledCharacter.normalDerivative_relPrime :
    IsRelPrime F (NormalChart.normal F) := by sorry
