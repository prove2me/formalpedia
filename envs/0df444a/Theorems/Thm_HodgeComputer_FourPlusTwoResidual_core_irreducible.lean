-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_core_irreducible
-- name    : HodgeComputer.FourPlusTwoResidual.core_irreducible
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:30.061708+00:00
-- url     : https://prove2.me/theorems/6f98d9af-b7a2-41c5-9179-54eef711d63d
-- title:
--   Irreducibility of the four-variable sextic core of four-plus-two-residual
-- statement:
--   The four-variable homogeneous sextic core polynomial
--
--   $$
--   H(x_0, x_1, y_0, y_1) = x_0^6 + \frac{5}{7} x_0^5 x_1 + \frac{5}{7} x_0^3 x_1 y_0 y_1 + \frac{10}{7} x_0 x_1^5 + \frac{10}{7} x_0 x_1 y_0^3 y_1 + x_1^6 + y_0^6 + \frac{5}{7} y_0^5 y_1 + \frac{15}{7} y_0 y_1^5 + y_1^6
--   $$
--
--   of `four-plus-two-residual` is irreducible in $\mathbb{C}[x_0, x_1, y_0, y_1]$.
--
--   Consequently, $H$ generates a prime ideal in the unique factorization domain $\mathbb{C}[x_0, x_1, y_0, y_1]$, so any homogeneous denominator $D$ satisfies $\gcd(H, D) = 1$ if and only if $H \nmid D$.
--
--   **Formalization Note** Proved via monic specialization in $x_0$ along $(x_1, y_0, y_1) = (0, T + r, 1)$ at a simple complex root $r$ of $z^6 + \frac{5}{7} z^5 + \frac{15}{7} z + 1 = 0$, applying Eisenstein's criterion at $(T) \subset \mathbb{C}[T]$.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` (`data/four-plus-two-residual/instance.rec`) and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoCore
import Mathlib.RingTheory.Polynomial.UniqueFactorization

theorem HodgeComputer.FourPlusTwoResidual.core_irreducible :
    Irreducible HodgeComputer.FourPlusTwoResidual.core := by sorry
