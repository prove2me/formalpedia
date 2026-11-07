-- Prove2me | Theorems.Thm_HodgeComputer_EightPlaneConfiguration_normalDerivative_relPrime
-- name    : HodgeComputer.EightPlaneConfiguration.normalDerivative_relPrime
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-06T23:04:54.599623+00:00
-- url     : https://prove2.me/theorems/ec27002a-4dc3-4e24-9d59-631e4b031f5d
-- title:
--   Eight-plane contact arrangement: the first normal derivative is a legal denominator
-- statement:
--   For the fixed sextic $F$ of the Eight planes contact-arrangement instance, let $P=\partial F/\partial X_0$. Then
--
--   $$\gcd_{\mathbb C[X_0,X_1,X_2,Y_0,Y_1,Y_2]}(F,P)=1.$$
--
--   Equivalently, every common polynomial divisor of $F$ and $P$ is a unit. This is the remaining admissibility assertion needed to use the first normal derivative as an auxiliary denominator. The source records smoothness via good reduction to the Fermat sextic modulo five; the present item isolates the precise complex-polynomial coprimality consequence used by the normal-chart reduction.
--
--   **Formalization Note.** Coprimality is `IsRelPrime` in the complex multivariate polynomial ring, rather than comaximality of the two generated ideals.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/eight-plane-configuration/checks.json, smoothness field; https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/eight-plane-configuration/instance.rec. Auxiliary coprimality consequence for the normal derivative chart.

import Definitions.Def_HodgeComputerEightPlaneConfiguration
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.EightPlaneConfiguration

theorem HodgeComputer.EightPlaneConfiguration.normalDerivative_relPrime :
    IsRelPrime F (NormalChart.normal F) := by sorry
