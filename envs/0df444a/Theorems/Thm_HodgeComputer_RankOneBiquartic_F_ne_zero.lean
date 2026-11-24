-- Prove2me | Theorems.Thm_HodgeComputer_RankOneBiquartic_F_ne_zero
-- name    : HodgeComputer.RankOneBiquartic.F_ne_zero
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T10:35:31.136591+00:00
-- url     : https://prove2.me/theorems/98523f89-7670-4396-9d28-6fe94da68c5c
-- title:
--   The rank-one-biquartic sextic is a nonzero polynomial
-- statement:
--   The sextic of the rank-one-biquartic instance is the nonzero polynomial
--
--   $$F=f(X_0,X_1,X_2)+g(Y_0,Y_1,Y_2)+\tfrac{5}{7}L(X)^2M(Y)$$
--
--   of $\mathbb C[X_0,X_1,X_2,Y_0,Y_1,Y_2]$, where
--
--   $$f(a,b,c)=a^6+b^6+c^6+\tfrac57\bigl(a^5b+2b^5c+3c^5a+a^2b^3c\bigr),$$
--   $$g(a,b,c)=a^6+b^6+c^6+\tfrac57\bigl(2a^5b+3b^5c+c^5a+2a^3bc^2\bigr),$$
--   $$L=X_0^2+X_0X_1+2X_1X_2+3X_2^2,\qquad M=Y_0^2+Y_0Y_1+2Y_1Y_2+3Y_2^2.$$
--
--   It is not the zero polynomial: the coefficient of the monomial $X_0^6$ in $F$ is $1$, all other coefficients are multiples of $1/7$, and $F$ is homogeneous of degree $6$.
--
--   The certificate framework requires $F\neq 0$ as the first field of every certificate (the hypersurface must be a genuine hypersurface, and $F^{q+1}$ must be a meaningful power), so this nonvanishing is a side condition of every certificate for this instance.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/docs/01-certificates.md, section "One denominator and the normalized equations", equations (E1) and (E2); data/rank-one-biquartic/instance.rec; the coefficient of X0^6 in the expanded polynomial

import Definitions.Def_HodgeComputerRankOneBiquartic

set_option autoImplicit false
open HodgeComputer HodgeComputer.RankOneBiquartic

theorem HodgeComputer.RankOneBiquartic.F_ne_zero : F ≠ 0 := by sorry
