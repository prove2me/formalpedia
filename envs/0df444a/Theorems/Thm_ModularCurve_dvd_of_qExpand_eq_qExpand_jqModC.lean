-- Prove2me | Theorems.Thm_ModularCurve_dvd_of_qExpand_eq_qExpand_jqModC
-- name    : ModularCurve.dvd_of_qExpand_eq_qExpand_jqModC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/56e6e4d6-88e7-58d7-9072-956c03834fe4
-- title:
--   Equality y(qᵈ)=jmath̄(q^N) forces d∣ N
-- statement:
--   Let $K$ be a field and let $d,N$ be natural numbers, both nonzero. Let $y$ be a Laurent series over $K$, i.e. an element of `LaurentSeries K` (a Hahn series over $K$ with value group $\mathbb{Z}$). Here [`ModularCurve.qExpand K n`](def/ModularCurve_X0.html#L25) denotes, for $n \neq 0$, the ring endomorphism of `LaurentSeries K` obtained by transporting supports along the injective, strictly monotone map $g \mapsto n g$ of $\mathbb{Z}$; concretely it is the substitution $q \mapsto q^{n}$, sending $\sum_m a_m q^{m}$ to $\sum_m a_m q^{nm}$. And [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15) is the Laurent series $q^{-1}$ times the image in $K$ of the integral power series `jNum` $=$ $E_4^{3}\cdot$ `dedekindEtaUnitInv`, that is the $q$-expansion of the modular invariant $j$ read with coefficients in $K$. The hypothesis is that the substitution $q \mapsto q^{d}$ applied to $y$ equals the substitution $q \mapsto q^{N}$ applied to this $j$-series: $y(q^{d}) = \bar\jmath(q^{N})$. The conclusion is that $d$ divides $N$. No assumption is made on the characteristic of $K$.
--
--   The statement isolates the elementary divisibility constraint imposed by comparing $q$-expansions in $q^{d}$ and in $q^{N}$, the leading coefficient of the $j$-expansion being $1$ in every characteristic. It is used in [`ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charP`](thm.html#ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charP), the non-membership of the $j$-series in the level-$N$ $q$-expansion function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_dvd_of_qExpand_eq_qExpand_jqModC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.dvd_of_qExpand_eq_qExpand_jqModC
    (K : Type*) [Field K] (d N : ℕ) [NeZero d] [NeZero N] (y : LaurentSeries K)
    (h : ModularCurve.qExpand K d y = ModularCurve.qExpand K N (ModularCurve.jqModC K)) : d ∣ N := by sorry
