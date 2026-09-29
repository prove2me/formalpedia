-- Prove2me | Theorems.Thm_ModularCurve_ord_jBar_dvd_three_of_odd
-- name    : ModularCurve.ord_jBar_dvd_three_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/efc33f0b-0fc6-5a31-9832-8b406ad89354
-- title:
--   Ramification over j=0 divides 3 for odd level
-- statement:
--   Let $N$ be a nonzero natural number which is odd, and let $F_N$ denote the field [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111): the subfield of the Laurent series field $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ generated over $\overline{\mathbb Q}$ by the coefficientwise images, under the map `coeffEmb` induced by $\mathbb Q \to \overline{\mathbb Q}$, of the elements of `modularFunctionFieldFull N`, the latter being the subfield of $\mathrm{LaurentSeries}(\mathbb Q)$ generated over $\mathbb Q$ by the family `divisorExpansions N`. Let $v$ be a place of $F_N$ over $\overline{\mathbb Q}$ in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), that is, a valuation subring of $F_N$ which contains the image of $\overline{\mathbb Q}$, is not all of $F_N$, and is a principal ideal ring; for $f \in F_N$, $v.\mathrm{ord}(f)$ is the integer $-\log$ of the value of $f$ under the adic valuation attached to the height-one prime of this subring. Let $\bar\jmath =$ [`ModularCurve.jBar N`](def/ModularCurve_MazurStepThreeInputs.html#L43) be the element of $F_N$ given by the coefficientwise image of the $q$-expansion `jq` of the modular invariant. Assuming $v.\mathrm{ord}(\bar\jmath) > 0$, the conclusion is that $v.\mathrm{ord}(\bar\jmath)$ divides $3$, hence equals $1$ or $3$.
--
--   This is the local ramification bound for the covering $X_0(N) \to X(1)$ above the point $j = 0$ in odd level: the ramification index at a place where the modular invariant vanishes is $1$ or $3$, reflecting the order-$3$ isotropy of $\rho = e^{2\pi i/3}$ in $\mathrm{PSL}_2(\mathbb Z)$. It is used in the computation of the genus of $X_0(N)$ for prime level and in the counting relation between the number of places above $j=0$ and $\psi(N)$; the companion statement at $j = 1728$ gives divisibility by $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jBar_dvd_three_of_odd.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_jBar_dvd_three_of_odd (N : ℕ) [NeZero N] (hN : Odd N)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hpos : 0 < v.ord (ModularCurve.jBar N)) :
    v.ord (ModularCurve.jBar N) ∣ 3 := by sorry
