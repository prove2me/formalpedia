-- Prove2me | Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
-- name    : ModularCurve.ord_qInftyPlaceBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/9fbf2f4a-fbc2-51f0-9678-51ab98df3e7d
-- title:
--   Order at the q-adic place equals q-expansion order
-- statement:
--   Let $L$ be a field and let $F$ be an intermediate field of the extension $L((q))/L$, where $L((q))$ is the field of formal Laurent series over $L$; for $f \in F$ write $\overline{f} \in L((q))$ for its image, denoted `qSeriesBar L F f`. Assume the hypothesis $h$: some $j \in F$ satisfies $\operatorname{order}(\overline{j}) = -1$, the order of a Hahn series being the index of its lowest nonzero coefficient (with the convention $\operatorname{order}(0)=0$). Under $h$ the set $\{f \in F : \operatorname{order}(\overline{f}) \ge 0\}$ is a valuation subring of $F$ containing $L$, distinct from $F$ and a principal ideal ring, hence defines a place `qInftyPlaceBar L F h` of $F$ over $L$ in the sense of the project's structure `Place`. The assertion is that for every $f \in F$ the associated normalised order, namely minus the logarithm of the value of $f$ under the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of that valuation ring, equals $\operatorname{order}(\overline{f})$. In particular both sides vanish at $f = 0$.
--
--   This identifies the valuation attached to the cusp $\infty$ on a curve presented through $q$-expansions with the elementary order of vanishing of the $q$-series, with no ramification factor, the hypothesis $h$ providing an element of $q$-order $-1$ whose inverse is a uniformiser. It is used in the computation of the order of $j$-type functions at the cusp and in the comparison of $\infty$ with its translates under field automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_qInftyPlaceBar.lean

import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_qInftyPlaceBar (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) (f : F) : (qInftyPlaceBar L F h).ord f = (qSeriesBar L F f).order := by sorry
