-- Prove2me | Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
-- name    : ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/0aa44a19-bcf8-5814-8aa4-ac1514c268ec
-- title:
--   Order of j(qᵈ) at the cusp at infinity
-- statement:
--   Let $N$ be a nonzero natural number and let $d$ be a nonzero natural number dividing $N$. Consider the Laurent series over $\mathbb{Q}$ obtained from `jq` $= q^{-1}\cdot j_{\mathrm{Num}}$ (the product of the Hahn series $q^{-1}$ with the power series whose coefficients are the integral coefficients of the $j$-function, cast to $\mathbb{Q}$) by applying `qExpand ℚ d`, the ring endomorphism of `LaurentSeries ℚ` that multiplies all exponents by $d$, i.e. the substitution $q \mapsto q^{d}$; then push this series forward coefficientwise along $\mathbb{Q} \to \overline{\mathbb{Q}}$ by `coeffEmb`. The assertion is that this element, viewed as an element of `modularFunctionFieldBar N` (the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$ inside `LaurentSeries (AlgebraicClosure ℚ)`, the membership being supplied by `coeffEmb_mem_laurentBaseChange` applied to `jqd_mem_full N hd`), has order $-d$ at the place `cuspInftyBar N`. Here the place is `qInftyPlaceBar` for this field, whose valuation subring is `qIntegersBar` and which is well-defined because the $q$-series of $j$ has order $-1$, and `Place.ord` denotes $-\log$ of the associated adic valuation, i.e. the normalised integer order function at that place.
--
--   This records the elementary cusp computation $\mathrm{ord}_{\infty}\, j(q^{d}) = -d$ for $d \mid N$, the pole order at the cusp $\infty$ of the degenerate modular function used to generate the function field of $X_0(N)$-type curves over $\overline{\mathbb{Q}}$. It feeds the divisor-theoretic bookkeeping at the cusp, being used in the analysis of prolongations of places and of integrality and residues of $j$ and $j(q^{d})$ along the level-one specialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand.lean

import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand (N : ℕ) [NeZero N] (d : ℕ) [NeZero d] (hd : d ∣ N) : (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hd)⟩ = -d := by sorry
