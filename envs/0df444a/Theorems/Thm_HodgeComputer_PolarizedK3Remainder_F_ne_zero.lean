-- Prove2me | Theorems.Thm_HodgeComputer_PolarizedK3Remainder_F_ne_zero
-- name    : HodgeComputer.PolarizedK3Remainder.F_ne_zero
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T22:43:45.943743+00:00
-- url     : https://prove2.me/theorems/9f9c8ea2-a928-409b-81a3-dfb08a102739
-- title:
--   Polarized K3 remainder: the sextic is nonzero
-- statement:
--   The exact sextic $F$ of the [polarized-k3-remainder](https://hodge.computer/#case/polarized-k3-remainder) instance is a nonzero polynomial in $\mathbb C[X_0,X_1,X_2,Y_0,Y_1,Y_2]$. Written in polarized coordinates $U=X+Y$, $V=X-Y$ it is
--
--   $$F=\tfrac12\bigl(f(U)+f(V)\bigr),$$
--
--   where $f(a,b,c)=a^6+b^6+c^6+\tfrac57(a^5b+2b^5c+3c^5a+a^2b^3c)$. In ambient monomials the leading term is $X_0^6$ with coefficient $1$, so $F$ is not the zero polynomial. The certificate framework requires $F\neq 0$ as the first field of every certificate: the hypersurface must be genuine, and the power $F^{q+1}$ must be meaningful.
-- source:
--   https://hodge.computer/#case/polarized-k3-remainder ; https://github.com/hodge-computer/sextics/tree/main/data/polarized-k3-remainder ; Diamond arXiv:2603.29157 certificate formalism

import Definitions.Def_HodgeComputerPolarizedK3Remainder

set_option autoImplicit false
open HodgeComputer HodgeComputer.PolarizedK3Remainder

theorem HodgeComputer.PolarizedK3Remainder.F_ne_zero : F ≠ 0 := by sorry
