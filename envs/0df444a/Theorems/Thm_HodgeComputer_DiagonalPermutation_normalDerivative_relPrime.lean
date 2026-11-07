-- Prove2me | Theorems.Thm_HodgeComputer_DiagonalPermutation_normalDerivative_relPrime
-- name    : HodgeComputer.DiagonalPermutation.normalDerivative_relPrime
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T03:44:21.399596+00:00
-- url     : https://prove2.me/theorems/7c999fc7-275e-4664-bccb-e63d5198b0ae
-- title:
--   Diagonal permutation: the first normal derivative is a legal denominator
-- statement:
--   For exactly the sextic $F$ of the diagonal-permutation instance, its first partial derivative is relatively prime to $F$:
--
--   $$\operatorname{IsRelPrime}_{\mathbb C[X_0,X_1,X_2,Y_0,Y_1,Y_2]}\left(F,\frac{\partial F}{\partial X_0}\right).$$
--
--   Every common polynomial divisor is therefore a unit. This is the denominator-admissibility condition for the normal-chart certificate construction. The assertion concerns polynomial relative primality, not comaximality.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/diagonal-permutation/instance.rec; derived exact coprimality consequence, proved by line specialization.

import Definitions.Def_HodgeComputerDiagonalPermutation
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.DiagonalPermutation

theorem HodgeComputer.DiagonalPermutation.normalDerivative_relPrime :
    IsRelPrime F (NormalChart.normal F) := by sorry
