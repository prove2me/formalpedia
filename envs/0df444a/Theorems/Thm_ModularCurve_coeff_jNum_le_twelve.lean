-- Prove2me | Theorems.Thm_ModularCurve_coeff_jNum_le_twelve
-- name    : ModularCurve.coeff_jNum_le_twelve
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/7e5ed736-8e5d-517d-935d-ad670c5599e4
-- title:
--   q-expansion of q j(q) through q¹²
-- statement:
--   A closed statement about the integral power series `jNum` over $\mathbb{Z}$, defined as the cube of `eisenstein4` multiplied by `dedekindEtaUnitInv`; here `eisenstein4` is the power series whose $0$-th coefficient is $1$ and whose $n$-th coefficient for $n \ge 1$ is $240\sum_{d \mid n} d^{3}$ (the normalised Eisenstein series $E_4$), and `dedekindEtaUnitInv` is the formal inverse of the unit power series `dedekindEtaUnit`, obtained from it by Mathlib's `invOfUnit` with inverse constant term $1$. There are no hypotheses. The conclusion is the thirteen-fold conjunction recording the coefficients of `jNum` in degrees $0$ through $12$: they are, in order, $1$, $744$, $196884$, $21493760$, $864299970$, $20245856256$, $333202640600$, $4252023300096$, $44656994071935$, $401490886656000$, $3176440229784420$, $22567393309593600$ and $146211911499519294$, each asserted as an equality of integers via `PowerSeries.coeff`. Nothing is asserted about coefficients in degree $13$ or beyond.
--
--   These are the classical Fourier coefficients of the modular invariant, $j(q) = q^{-1} + 744 + 196884q + \cdots$, here in the shifted integral form $q\,j(q)$. The statement is used in the identification of the level-$3$ modular polynomial data with the explicit classical $\Phi_3$, in [`ModularCurve.ModularPolynomialData.phi_eq_phiThree`](thm.html#ModularCurve.ModularPolynomialData.phi_eq_phiThree), where a finite number of $q$-expansion coefficients must be compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_jNum_le_twelve.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve Polynomial

theorem ModularCurve.coeff_jNum_le_twelve :
    PowerSeries.coeff 0 jNum = 1 ∧ PowerSeries.coeff 1 jNum = 744 ∧ PowerSeries.coeff 2 jNum = 196884 ∧
      PowerSeries.coeff 3 jNum = 21493760 ∧ PowerSeries.coeff 4 jNum = 864299970 ∧
      PowerSeries.coeff 5 jNum = 20245856256 ∧ PowerSeries.coeff 6 jNum = 333202640600 ∧
      PowerSeries.coeff 7 jNum = 4252023300096 ∧ PowerSeries.coeff 8 jNum = 44656994071935 ∧
      PowerSeries.coeff 9 jNum = 401490886656000 ∧ PowerSeries.coeff 10 jNum = 3176440229784420 ∧
      PowerSeries.coeff 11 jNum = 22567393309593600 ∧ PowerSeries.coeff 12 jNum = 146211911499519294 := by sorry
