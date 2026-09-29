-- Prove2me | Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
-- name    : ModularCurve.ord_cuspInftyBar_coeffEmb_jq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/88bc0883-9302-5fa7-90b2-08d4d596aa3c
-- title:
--   The q-expansion of j has order -1 at ∞
-- statement:
--   Let $N$ be a non-zero natural number. Write $\bar{\mathbb{Q}}$ for `AlgebraicClosure ℚ`, and let `modularFunctionFieldBar N` be the intermediate field `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)` of $\bar{\mathbb{Q}}((q))$, i.e. the base change to $\bar{\mathbb{Q}}$ of the full-level-$N$ modular function field sitting inside $\mathbb{Q}((q))$. Let `jq` be the Laurent series over $\mathbb{Q}$ given by `HahnSeries.single (-1) 1` times the image of the power series `jNumQ` under `HahnSeries.ofPowerSeries`, that is, $q^{-1}$ times the numerator power series of the modular invariant $j$; applying the coefficientwise ring homomorphism `coeffEmb (AlgebraicClosure ℚ)`, induced by $\mathbb{Q} \to \bar{\mathbb{Q}}$, produces an element of $\bar{\mathbb{Q}}((q))$, which by `coeffEmb_mem_laurentBaseChange` applied to `jq_mem_full N` lies in `modularFunctionFieldBar N`. Let `cuspInftyBar N` be the place of `modularFunctionFieldBar N` over $\bar{\mathbb{Q}}$ obtained from `qInftyPlaceBar` with this element as the witness of order $-1$; a `Place` consists of a valuation subring containing the image of the base field, not equal to the whole field, whose ring is a principal ideal ring. The assertion is that the order function `ord` of this place — minus the `WithZero` logarithm of the adic valuation attached to the valuation subring — takes the value $-1$ on the above element.
--
--   This records that the $q$-expansion of the modular invariant $j$ has a simple pole at the cusp $\infty$ of the full level-$N$ modular curve over $\bar{\mathbb{Q}}$, so that $\infty$ is unramified over the $j$-line. It is used throughout the treatment of divisors, residues and rationality on the modular curves, for instance in the analysis of poles of functions pulled back along the Fricke involution and in the construction of rational cusp-regular functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq.lean

import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspInftyBar_coeffEmb_jq (N : ℕ) [NeZero N] : (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -1 := by sorry
