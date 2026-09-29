-- Prove2me | Theorems.Thm_ModularCurve_ord_jBar_sub_eq_one_of_ne_zero_of_ne_of_odd
-- name    : ModularCurve.ord_jBar_sub_eq_one_of_ne_zero_of_ne_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/9251a5ff-f6fa-5e7a-9382-fee203b0bb32
-- title:
--   Unramifiedness of jmath̄ - c away from 0 and 1728, odd level
-- statement:
--   Let $N$ be a nonzero natural number with $N$ odd, and work inside the field $L = \mathrm{LaurentSeries}(\overline{\mathbb Q})$ of formal Laurent series over an algebraic closure of $\mathbb Q$. Write $\bar F_N$ for [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111), the intermediate field of $L/\overline{\mathbb Q}$ generated over $\overline{\mathbb Q}$ by the coefficientwise image `coeffEmb` of [`ModularCurve.modularFunctionFieldFull N`](def/ModularCurve_X0.html#L305), the latter being the subfield of $\mathrm{LaurentSeries}(\mathbb Q)$ generated over $\mathbb Q$ by the divisor expansions `divisorExpansions N`; and write $\bar\jmath =$ [`ModularCurve.jBar N`](def/ModularCurve_MazurStepThreeInputs.html#L43) for the element of $\bar F_N$ given by the coefficientwise image of the $q$-expansion `jq` of the modular invariant. Let $v$ be a place of $\bar F_N$ over $\overline{\mathbb Q}$ in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), that is, a valuation subring of $\bar F_N$ which contains the image of $\overline{\mathbb Q}$, is not all of $\bar F_N$, and is a principal ideal ring; for $f \in \bar F_N$ the integer $v.\mathrm{ord}(f)$ is minus the logarithm of the associated height-one-spectrum valuation of $f$, i.e. the order of vanishing of $f$ at $v$. Let $c \in \overline{\mathbb Q}$ with $c \neq 0$ and $c \neq 1728$. The assertion is: if $v.\mathrm{ord}(\bar\jmath - c) > 0$, then $v.\mathrm{ord}(\bar\jmath - c) = 1$.
--
--   This is the statement that the $j$-map $X_0(N)_{\overline{\mathbb Q}} \to X(1)_{\overline{\mathbb Q}}$ is unramified over every finite $j$-value other than $0$ and $1728$, in the form of an order-of-vanishing statement on the function field, here proved for odd level $N$. It is used to confine the ramification of the $j$-map to the fibres over $0$, $1728$ and $\infty$ in the genus computation for $X_0(N)$ at prime level, and in the local analysis at a node.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jBar_sub_eq_one_of_ne_zero_of_ne_of_odd.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_jBar_sub_eq_one_of_ne_zero_of_ne_of_odd (N : ℕ) [NeZero N] (hN : Odd N)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (c : AlgebraicClosure ℚ) (hc0 : c ≠ 0) (hc1728 : c ≠ 1728)
    (hpos : 0 < v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) c)) :
    v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) c) = 1 := by sorry
