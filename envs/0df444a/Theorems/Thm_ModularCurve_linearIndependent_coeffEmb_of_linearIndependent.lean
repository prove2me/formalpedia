-- Prove2me | Theorems.Thm_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent
-- name    : ModularCurve.linearIndependent_coeffEmb_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/83d3b540-c0d9-5c35-91e1-a047de94670a
-- title:
--   Coefficient extension preserves linear independence of Laurent series
-- statement:
--   Let $L$ be a field of characteristic zero (so that $L$ is canonically a $\mathbb{Q}$-algebra), let $\iota$ be an index type, and let $v : \iota \to \mathrm{LaurentSeries}\,\mathbb{Q}$ be a family of formal Laurent series with rational coefficients, i.e. of Hahn series over $\mathbb{Z}$ with coefficients in $\mathbb{Q}$. Assume that $v$ is linearly independent over $\mathbb{Q}$. The conclusion is that the family $i \mapsto \mathrm{coeffEmb}\,L\,(v\,i)$ is linearly independent over $L$ in $\mathrm{LaurentSeries}\,L$. Here `coeffEmb L` is the ring homomorphism $\mathrm{LaurentSeries}\,\mathbb{Q} \to \mathrm{LaurentSeries}\,L$ given by `coeffMap (algebraMap ℚ L)`, that is, the map which applies the structure morphism $\mathbb{Q} \to L$ to every coefficient of a Laurent series, this coefficientwise operation being additive and multiplicative and sending $0$ and $1$ to $0$ and $1$. No finiteness hypothesis is imposed on $L$, and $\iota$ is an arbitrary type, with the index and coefficient universes independent.
--
--   This is the injectivity half of the statement that $L$ and $\mathbb{Q}((q))$ are linearly disjoint over $\mathbb{Q}$ inside $L((q))$: any $\mathbb{Q}$-basis of a $\mathbb{Q}$-subspace of $\mathbb{Q}((q))$ remains $L$-free after extension of coefficients. It is used in the analysis of $q$-expansions on modular curves, in particular by the results producing maximal charts over supersingular places at level structures with $\ell = 2, 3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

universe u v

theorem ModularCurve.linearIndependent_coeffEmb_of_linearIndependent
    (L : Type u) [Field L] [CharZero L]
    {ι : Type v} {v : ι → LaurentSeries ℚ} (hv : LinearIndependent ℚ v) :
    LinearIndependent L (fun i => coeffEmb L (v i)) := by sorry
