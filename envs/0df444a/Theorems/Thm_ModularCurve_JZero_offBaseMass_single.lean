-- Prove2me | Theorems.Thm_ModularCurve_JZero_offBaseMass_single
-- name    : ModularCurve.JZero.offBaseMass_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/ac5b730c-e77c-588d-982c-ea929e5e83ff
-- title:
--   Off-cusp mass of a one-point divisor
-- statement:
--   Let $N$ be a non-zero natural number and work with $\overline{F}_N =$ `modularFunctionFieldBar N`, the intermediate field of $\overline{\mathbb{Q}}\,((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the elements of `modularFunctionFieldFull N`, itself the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions of level $N$. A place of $\overline{F}_N$ over $\overline{\mathbb{Q}}$ is, in the sense of the structure `Place`, a valuation subring of $\overline{F}_N$ containing the image of $\overline{\mathbb{Q}}$, distinct from the whole field, and a principal ideal ring; divisors are the finitely supported functions from such places to $\mathbb{Z}$. Let $v$ be such a place with $v \neq$ `cuspInftyBar N`, the place at the cusp given by the $q$-adic valuation subring `qIntegersBar` (witnessed by the image of the $q$-expansion of $j$, of order $-1$), and let $n$ be an integer. The assertion is that `offBaseMass N`, the sum of the coefficients of a divisor after erasing its value at the cusp, takes the value $n$ on the divisor `Finsupp.single v n`, i.e. $n$ times the one-point divisor at $v$.
--
--   This is the computation of the off-cusp mass of a single-point divisor, one of the elementary bookkeeping identities for the masses attached to divisors on the modular curve, which are additive and blind to the cusp. It is used in [`ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm`](thm.html#ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm), where masses of divisor representatives of classes in $J_0(N)$ are tracked along sums, integer multiples and padding by the cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_offBaseMass_single.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.offBaseMass_single (N : ℕ) [NeZero N] {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : v ≠ cuspInftyBar N) (n : ℤ) :
    offBaseMass N (Finsupp.single v n) = n := by sorry
