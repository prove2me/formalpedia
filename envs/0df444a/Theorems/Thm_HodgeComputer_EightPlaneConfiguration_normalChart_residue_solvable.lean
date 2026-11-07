-- Prove2me | Theorems.Thm_HodgeComputer_EightPlaneConfiguration_normalChart_residue_solvable
-- name    : HodgeComputer.EightPlaneConfiguration.normalChart_residue_solvable
-- status  : Open
-- author  : @shivm
-- created : 2026-11-06T23:04:53.56495+00:00
-- url     : https://prove2.me/theorems/7717b7b7-3bd2-4a33-bb31-30771c804a1d
-- title:
--   Eight-plane contact arrangement: solve the scalar normal-chart residue equation
-- statement:
--   Fix exactly $F$ and $A=X_0^3Y_0^3$ from the Eight planes contact-arrangement instance. There exist polynomials $S,W_1,\ldots,W_5,Q$ over $\mathbb C$, with $S\ne0$, $S$ homogeneous of degree $e=\deg S$ and relatively prime to $F$, and each $W_j$ homogeneous of degree $e+1$, such that
--
--   $$\mathcal R_{F,A}(S,W)=FQ.$$
--
--   Write $z=(X_0,X_1,X_2,Y_0,Y_1,Y_2)$, $F_i=\partial_i F$, $P=F_0$, and use subscripts on $P,S,A$ for partial derivatives. For five polynomials $W_1,\ldots,W_5$, define
--
--   $$
--   \begin{aligned}
--   \mathcal R_{F,A}(S,W)={}&S^2(PA_0-AP_0)\\
--   &+\sum_{j=1}^5\left[P^2S\,\partial_jW_j-PSF_j\,\partial_0W_j
--   +\bigl(F_j(SP_0+PS_0)-P(SP_j+PS_j)\bigr)W_j\right].
--   \end{aligned}
--   $$
--
--   This is the remaining scalar residue-solvability problem in the normal-chart reduction of the mission. No bound is imposed on $e$, and $Q$ may be nonzero. For each fixed $S$, it is a linear equation in the coefficients of $W_1,\ldots,W_5,Q$ with prescribed source term. Finding a suitable legal $S$ remains part of the problem.
--
--   **Formalization Note.** This item is a derived open subproblem, not a claim that the source supplies a certificate for the instance. The companion normal-derivative coprimality lemma and the proved construction reconnect it to the exact original mission target.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/eight-plane-configuration/instance.rec; https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/docs/01-certificates.md, "One denominator and the normalized equations", E1 and E2. Derived open normal-chart subproblem for this exact instance.

import Definitions.Def_HodgeComputerEightPlaneConfiguration
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.EightPlaneConfiguration

theorem HodgeComputer.EightPlaneConfiguration.normalChart_residue_solvable :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 1)) ∧
      NormalChart.residue F A S W = F * Q := by sorry
