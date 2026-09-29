-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFull_prime
-- name    : ModularCurve.relfinrank_modularFunctionFieldFull_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/cae1c289-b0cf-580e-8561-b8941adeeb16
-- title:
--   Degree ℓ+1 of the full level-ℓ modular function field
-- statement:
--   Let $\ell$ be a natural number carrying the typeclass hypothesis that it is prime. Work inside the field $\mathrm{LaurentSeries}\,\mathbb{Q}$ of formal Laurent series in $q$ over $\mathbb{Q}$, and let $jq$ denote the element $q^{-1}\cdot jNumQ$, where $jNumQ$ is the power series `jNum` with its integer coefficients pushed to $\mathbb{Q}$; thus $jq$ is the $q$-expansion of the modular invariant $j$. Let $F$ be the intermediate field `modularFunctionFieldFull ℓ`, namely the subfield of $\mathrm{LaurentSeries}\,\mathbb{Q}$ generated over $\mathbb{Q}$ by the set of all substitutions $qExpand\ \mathbb{Q}\ d\ jq$ (the operation $q \mapsto q^{d}$) for nonzero divisors $d$ of $\ell$; for $\ell$ prime these are the expansions of $j$ and of $j(\ell\tau)$. The assertion is that the relative degree `IntermediateField.relfinrank` of $F$ over the intermediate field $\mathbb{Q}(jq)$ equals $\ell + 1$. Since the divisor $d = 1$ contributes $jq$ itself, $\mathbb{Q}(jq) \subseteq F$ and this relative degree is the degree $[F : \mathbb{Q}(jq)]$.
--
--   This is the classical statement that the function field of $X_0(\ell)$ has degree $\ell+1$ over $\mathbb{Q}(j)$ for $\ell$ prime, obtained here without recourse to the irreducibility of the modular polynomial $\Phi_\ell(j,Y)$: the degree is transported from the corresponding geometric degree over $\overline{\mathbb{Q}}$, where $jq$ is transcendental. It supports the computations of the Hecke correspondence and of the cuspidal divisors at prime level, notably [`ModularCurve.heckeAlphaBar_frickeInvolutionBar_sq`](thm.html#ModularCurve.heckeAlphaBar_frickeInvolutionBar_sq), [`ModularCurve.heckeDivBar_cuspidalDivisor_of_prime`](thm.html#ModularCurve.heckeDivBar_cuspidalDivisor_of_prime) and [`ModularCurve.heckeDivBar_cuspidalDivisor_self_of_prime`](thm.html#ModularCurve.heckeDivBar_cuspidalDivisor_self_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_modularFunctionFieldFull_prime.lean

import Definitions.Def_ModularCurve_QAdicPlace
import Mathlib.FieldTheory.Relrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.relfinrank_modularFunctionFieldFull_prime (ℓ : ℕ) [Fact ℓ.Prime] : IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularFunctionFieldFull ℓ) = ℓ + 1 := by sorry
