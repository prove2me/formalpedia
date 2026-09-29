-- Prove2me | Theorems.Thm_ModularCurve_linearIndependent_coeffMap_algebraMap
-- name    : ModularCurve.linearIndependent_coeffMap_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/79fbe622-b32a-51f7-a680-1c48a361819e
-- title:
--   Base change preserves linear independence of Laurent series
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $\iota$ be an index type, and let $v : \iota \to \mathrm{LaurentSeries}\ K$ be a family of formal Laurent series over $K$, i.e. of Hahn series over $K$ with value group $\mathbb{Z}$. Assume that $v$ is linearly independent over $K$. Then the family obtained by pushing each $v_i$ forward coefficientwise along the structure map $K \to L$ is linearly independent over $L$ in $\mathrm{LaurentSeries}\ L$: here, for a ring homomorphism $f : R \to S$, `coeffMap f` is the ring homomorphism $\mathrm{LaurentSeries}\ R \to \mathrm{LaurentSeries}\ S$ sending a series to its image under applying $f$ to every coefficient (the Hahn series `map` construction, whose multiplicativity, additivity and unitality are the content of the definition), so the asserted family is $i \mapsto \sum_n f(c_{i,n}) q^n$ where $v_i = \sum_n c_{i,n} q^n$ and $f = \mathrm{algebraMap}\ K\ L$. In other words, $L$ and $K(\!(q)\!)$ are linearly disjoint over $K$ inside $L(\!(q)\!)$.
--
--   This is the linear disjointness of a field extension $L/K$ from the Laurent series field $K(\!(q)\!)$ over $K$, in the form needed to transfer $K$-freeness of a family of $q$-expansions to $L$-freeness after coefficientwise base change. It is used in the construction of the family contexts for multiplicative coverings of modular curves, where $q$-expansions with coefficients in a small field are compared with their images in a larger coefficient field ([`ModularCurve.MultCovering.exists_famCtx`](thm.html#ModularCurve.MultCovering.exists_famCtx), [`ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue`](thm.html#ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue) and [`ModularCurve.MultCovering.infChart_residue_eq_ssPolyBar_mul_of_orthogonal`](thm.html#ModularCurve.MultCovering.infChart_residue_eq_ssPolyBar_mul_of_orthogonal)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_linearIndependent_coeffMap_algebraMap.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.linearIndependent_coeffMap_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L]
    {ι : Type*} (v : ι → LaurentSeries K) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => coeffMap (algebraMap K L) (v i)) := by sorry
