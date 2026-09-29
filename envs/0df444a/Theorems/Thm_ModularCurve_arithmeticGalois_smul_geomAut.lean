-- Prove2me | Theorems.Thm_ModularCurve_arithmeticGalois_smul_geomAut
-- name    : ModularCurve.arithmeticGalois_smul_geomAut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/e7511cab-c866-5efe-a3c1-6a40fb0e60f8
-- title:
--   Arithmetic semilinear action commutes with geometric automorphisms
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure which makes it algebraic over $\mathbb{Q}$, and let $F_0$ be an intermediate field of $\mathbb{Q}$ in the field $\mathrm{LaurentSeries}\,\mathbb{Q}$ of formal Laurent series over $\mathbb{Q}$. Write $L\cdot F_0$ for `laurentBaseChange L F₀`, the intermediate field of $L$ in $\mathrm{LaurentSeries}\,L$ generated over $L$ by the image of $F_0$ under the coefficientwise extension `coeffEmb L` of $\mathbb{Q}\to L$. Let $\tau$ be a $\mathbb{Q}$-algebra automorphism of $L$ and $\sigma$ a $\mathbb{Q}$-algebra automorphism of $F_0$, and let $x\in L\cdot F_0$. Here `arithmeticGalois F₀ τ` is the element of the group `SemilinearAut L (laurentBaseChange L F₀)` of pairs (ring automorphism of $L\cdot F_0$, ring automorphism of $L$) compatible with the structure map, whose first component is the coefficientwise application of $\tau$ and whose second component is $\tau$ itself; and `geomAut L F₀ σ` is the $L$-algebra automorphism of $L\cdot F_0$ obtained by transporting $\mathrm{id}_L\otimes\sigma$ along the isomorphism `baseChangeEquiv L F₀ : L ⊗[ℚ] F₀ ≃ₐ[L] laurentBaseChange L F₀`. The assertion is that these two operations commute on $x$: applying `geomAut L F₀ σ` and then the semilinear action of `arithmeticGalois F₀ τ` gives the same element as applying the action of `arithmeticGalois F₀ τ` first and then `geomAut L F₀ σ`.
--
--   This is the commutation of the arithmetic action of $\mathrm{Aut}_{\mathbb{Q}}(L)$ on a constant-field extension $L\cdot F_0$ of a function field with the geometric automorphisms coming from $\mathrm{Aut}_{\mathbb{Q}}(F_0)$, stated for the bundled semilinear action rather than for the underlying ring automorphism. It is the form in which the commutation hypothesis is fed to the statements about Galois actions on places, specialisations and degree-zero Picard groups of such base-changed curves, and so to automorphisms such as the Atkin–Lehner involutions acting on the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_arithmeticGalois_smul_geomAut.lean

import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.arithmeticGalois_smul_geomAut (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (τ : L ≃ₐ[ℚ] L) (σ : F₀ ≃ₐ[ℚ] F₀) (x : laurentBaseChange L F₀) : arithmeticGalois F₀ τ • geomAut L F₀ σ x = geomAut L F₀ σ (arithmeticGalois F₀ τ • x) := by sorry
