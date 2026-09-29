-- Prove2me | Theorems.Thm_ModularCurve_arithmeticRingAut_geomAut
-- name    : ModularCurve.arithmeticRingAut_geomAut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/eb1f3d01-a929-5a1f-aaea-b68a54b5e045
-- title:
--   Coefficientwise and geometric Galois actions on L· F₀ commute
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure with $L$ algebraic over $\mathbb{Q}$, and let $F_0$ be an intermediate field of $\mathbb{Q}$ in the field of Laurent series $\mathbb{Q}((q))$. Write `laurentBaseChange L F₀` for the intermediate field of $L$ in $L((q))$ generated over $L$ by the image of $F_0$ under the coefficientwise embedding $\mathbb{Q}((q)) \to L((q))$ induced by $\mathbb{Q} \to L$. Two automorphisms of this field are at issue: for $\tau : L \simeq_{\mathbb{Q}} L$, the ring automorphism `arithmeticRingAut F₀ τ` given by applying $\tau$ to each Laurent coefficient; and for $\sigma : F_0 \simeq_{\mathbb{Q}} F_0$, the $L$-algebra automorphism `geomAut L F₀ σ` obtained by transporting $\mathrm{id}_L \otimes \sigma$ on $L \otimes_{\mathbb{Q}} F_0$ along the $L$-algebra isomorphism `baseChangeEquiv L F₀` $: L \otimes_{\mathbb{Q}} F_0 \simeq$ `laurentBaseChange L F₀`. The assertion is that for every element $x$ of `laurentBaseChange L F₀` one has $\tau_*(\sigma_*(x)) = \sigma_*(\tau_*(x))$, i.e. the two automorphisms commute pointwise, hence as automorphisms.
--
--   This records that the arithmetic (coefficientwise) and geometric (base-changed) Galois actions on the constant-field extension $L\cdot F_0$ of a field of modular functions act on the two factors of $L \otimes_{\mathbb{Q}} F_0$ independently. It is used to assemble the two actions into a single group action, as in [`ModularCurve.arithmeticGalois_smul_geomAut`](thm.html#ModularCurve.arithmeticGalois_smul_geomAut).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_arithmeticRingAut_geomAut.lean

import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.arithmeticRingAut_geomAut (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (τ : L ≃ₐ[ℚ] L) (σ : F₀ ≃ₐ[ℚ] F₀) (x : laurentBaseChange L F₀) : arithmeticRingAut F₀ τ (geomAut L F₀ σ x) = geomAut L F₀ σ (arithmeticRingAut F₀ τ x) := by sorry
