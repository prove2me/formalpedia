-- Prove2me | Theorems.Thm_ModularCurve_ord_cuspInftyBar
-- name    : ModularCurve.ord_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/f78dd74f-c083-5354-9c07-2743db46778f
-- title:
--   Order at the cusp ∞ is the q-order
-- statement:
--   Let $N$ be a positive natural number and let $f$ be an element of `modularFunctionFieldBar N`, the intermediate field $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$ obtained as `laurentBaseChange` of `modularFunctionFieldFull N`, that is, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images under `coeffEmb` of the $\mathbb{Q}$-subfield $\mathbb{Q}(\,\mathrm{divisorExpansions}\,N\,) \subseteq \mathbb{Q}((q))$. On this field `cuspInftyBar N` is the place in the sense of the project's `Place` structure, namely a valuation subring containing the image of the base field, distinct from the whole field and a principal ideal ring: it is `qInftyPlaceBar` for the subring `qIntegersBar`, with the required witness of an element of $q$-order $-1$ given by the coefficientwise image of `jq`, which lies in the base change and has order $-1$. The assertion is that the associated order function, defined as minus the logarithm of the value of $f$ under the height-one-spectrum valuation attached to this valuation subring, coincides with the Hahn series order of $f$ regarded as an element of $\overline{\mathbb{Q}}((q))$, i.e. the $q$-adic order of vanishing of the Laurent expansion of $f$.
--
--   This identifies the valuation attached to the cusp $\infty$ on the base-changed modular curve of level $N$ with the elementary order of vanishing of a $q$-expansion, so that divisors supported at $\infty$ can be computed directly from Fourier expansions. It is used throughout the subsequent analysis of places and their prolongations, for instance in the statements governing the behaviour of specialisations at the cusp and in the sum formulae for orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_cuspInftyBar.lean

import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspInftyBar (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N) : (cuspInftyBar N).ord f = (f : LaurentSeries (AlgebraicClosure ℚ)).order := by sorry
