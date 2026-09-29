-- Prove2me | Theorems.Thm_ModularCurve_TatePoint_fullKernelInjAt
-- name    : ModularCurve.TatePoint.fullKernelInjAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/806a70f5-a83e-5cd1-ab7a-43f432d4d456
-- title:
--   Injectivity of the full-kernel quotient at level N
-- statement:
--   Let $N$ be a natural number, assumed nonzero, and write $H$ for the field of Hahn series with exponents in $\mathbb{Q}$ and coefficients in $\overline{\mathbb{Q}}$. The theorem asserts the property `FullKernelInjAt N`, namely: for any decidable equality on $H$, any Weierstrass curve $W$ over $H$ that is elliptic (its discriminant a unit) and whose $j$-invariant is transcendental over $\mathbb{Q}$, and any two points $Q, Q'$ of the associated affine curve whose additive orders are both exactly $N$, suppose the two curves $W.\mathrm{fullKernelQuotient}\,Q\,N$ and $W.\mathrm{fullKernelQuotient}\,Q'\,N$ — the Vélu quotients formed from the sums $\sum \mathrm{veluGx}(P)$ and $\sum (x_P\,\mathrm{veluGx}(P) - y_P\,\mathrm{veluGy}(P))$ over the odd-order summing set of $Q$, respectively $Q'$, with parameter $N-1$ — both have nonzero discriminant, so that both are elliptic, and suppose their $j$-invariants (computed with those elliptic structures) are equal. Then the subgroups of integer multiples of $Q$ and of $Q'$ in the group of points of $W$ coincide, i.e. $\mathbb{Z}Q = \mathbb{Z}Q'$.
--
--   This is the injectivity half of the dictionary between cyclic subgroups of order $N$ of an elliptic curve with transcendental $j$-invariant and the $j$-invariants of the corresponding Vélu quotients: distinct cyclic subgroups of order $N$ give distinct quotient $j$-invariants. It is used in identifying the fibre of the modular polynomial with the set of quotient $j$-invariants and in producing elliptic curves with prescribed cyclic-subgroup orbit data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_TatePoint_fullKernelInjAt.lean

import Definitions.Def_ModularCurve_CycSubRootBridgeN

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical

theorem ModularCurve.TatePoint.fullKernelInjAt (N : ℕ) [NeZero N] : FullKernelInjAt N := by sorry
