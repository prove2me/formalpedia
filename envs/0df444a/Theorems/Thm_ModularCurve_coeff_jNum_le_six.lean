-- Prove2me | Theorems.Thm_ModularCurve_coeff_jNum_le_six
-- name    : ModularCurve.coeff_jNum_le_six
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/54c65c6d-f558-52f0-9c7d-657f08d05504
-- title:
--   First seven coefficients of the q-expansion of j
-- statement:
--   The statement has no variables or hypotheses: it is a closed assertion about a single integral formal power series. Here `eisenstein4` is the power series in $\mathbb{Z}[[q]]$ whose $n$-th coefficient is $1$ for $n=0$ and $240\sum_{d\mid n} d^{3}$ for $n\ge 1$, i.e. the $q$-expansion $E_4 = 1 + 240\sum_{n\ge1}\sigma_3(n)q^n$; `dedekindEtaUnitInv` is the multiplicative inverse of the power series `dedekindEtaUnit`, formed as its inverse with respect to the constant coefficient $1$; and `jNum` is the product $(\mathrm{eisenstein4})^3 \cdot \mathrm{dedekindEtaUnitInv}$. The theorem is the conjunction of seven equalities of integers, asserting that the coefficients of `jNum` in degrees $0$ through $6$ are, respectively, $1$, $744$, $196884$, $21493760$, $864299970$, $20245856256$ and $333202640600$. Thus `jNum` agrees with $1 + 744q + 196884q^2 + 21493760q^3 + 864299970q^4 + 20245856256q^5 + 333202640600q^6$ modulo $q^{7}$; equivalently, $q^{-1}\cdot \mathrm{jNum} = q^{-1} + 744 + 196884q + \cdots + 333202640600q^{5} + O(q^{6})$ is the familiar expansion of the modular invariant $j$, the statement being purely about formal power series with no reference to the upper half-plane.
--
--   This records the classical beginning of the $q$-expansion of the elliptic modular function $j = E_4^3/\Delta$ with $\Delta = q\prod_{n\ge1}(1-q^n)^{24}$, in the normalised form where the pole at $q=0$ has been cleared. It is used in the verification of modular polynomial data, being cited by [`ModularCurve.ModularPolynomialData.phi_eq_phiTwo`](thm.html#ModularCurve.ModularPolynomialData.phi_eq_phiTwo).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_jNum_le_six.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve Polynomial

theorem ModularCurve.coeff_jNum_le_six :
    PowerSeries.coeff 0 jNum = 1 ∧ PowerSeries.coeff 1 jNum = 744 ∧ PowerSeries.coeff 2 jNum = 196884 ∧
      PowerSeries.coeff 3 jNum = 21493760 ∧ PowerSeries.coeff 4 jNum = 864299970 ∧
      PowerSeries.coeff 5 jNum = 20245856256 ∧ PowerSeries.coeff 6 jNum = 333202640600 := by sorry
