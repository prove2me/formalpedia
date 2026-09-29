-- Prove2me | Theorems.Thm_ModularCurve_CuspSpace_classification
-- name    : ModularCurve.CuspSpace.classification
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/21f1ac5a-0bf2-5001-b80d-4ad0892d4673
-- title:
--   Classification of the cusps of Γ₀(N)
-- statement:
--   For a natural number $N$ with $N \neq 0$, the predicate [`ModularCurve.CuspSpace.Classification N`](def/ModularCurve_CuspSpace.html#L258) holds, that is: there exists a bijection between the cusp space of level $N$ and the dependent sum, over the divisors $d$ of $N$, of the unit groups $(\mathbb{Z}/\gcd(d, N/d))^{\times}$. Here the cusp space [`ModularCurve.CuspSpace N`](def/ModularCurve_CuspSpace.html#L103) is the quotient of $\mathbb{P}^1(\mathbb{Q})$, realised as the one-point extension `OnePoint ℚ` of $\mathbb{Q}$, by the orbit equivalence relation for the action of the subgroup `Gamma0Q N` of $\mathrm{GL}_2(\mathbb{Q})$, namely the image of the congruence subgroup $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$ under the map `mapGL ℚ` into $\mathrm{GL}_2(\mathbb{Q})$; the indexing type on the right is `N.divisors`, the divisors of $N$, and for each such $d$ the fibre is the group of units of $\mathbb{Z}/\gcd(d, N/d)\mathbb{Z}$. The conclusion is the nonemptiness of the type of such equivalences, so it asserts the existence of a bijection rather than exhibiting a designated one; in particular no compatibility of the bijection with the denominator $d$ or the numerator residue is part of the assertion.
--
--   This is the classical count and classification of the cusps of $\Gamma_0(N)$, by a denominator divisor $d \mid N$ together with a numerator class in $(\mathbb{Z}/\gcd(d,N/d))^{\times}$ (Diamond–Shurman, Prop. 3.8.3). It is obtained from the normal-form results for points of $\mathbb{P}^1(\mathbb{Q})$ modulo $\Gamma_0(N)$ and is used to compute the cardinality of the cusp space, in [`ModularCurve.CuspSpace.card_cuspSpace_eq_cuspCount`](thm.html#ModularCurve.CuspSpace.card_cuspSpace_eq_cuspCount).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CuspSpace_classification.lean

import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open OnePoint

theorem ModularCurve.CuspSpace.classification {N : ℕ} (hN : N ≠ 0) :
    ModularCurve.CuspSpace.Classification N := by sorry
