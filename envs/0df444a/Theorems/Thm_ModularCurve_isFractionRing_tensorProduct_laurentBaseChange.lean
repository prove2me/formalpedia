-- Prove2me | Theorems.Thm_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange
-- name    : ModularCurve.isFractionRing_tensorProduct_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/1aeac8db-93cf-5135-8e4d-87d28948256c
-- title:
--   Compositum L· F₀ in L((q)) as Frac(L⊗_ℚF₀)
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure and let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$, i.e. a subfield of the field of Laurent series `LaurentSeries ℚ` containing $\mathbb{Q}$. Write $\iota =$ `coeffEmb L` for the ring homomorphism $\mathbb{Q}((q)) \to L((q))$ obtained by applying the structure map $\mathbb{Q} \to L$ to each coefficient, and let `laurentBaseChange L F₀` be the intermediate field of $L \subseteq L((q))$ generated over $L$ by the set $\iota(F_0)$. Let $\beta =$ `baseChangeHom L F₀` be the $L$-algebra homomorphism $L \otimes_{\mathbb{Q}} F_0 \to L((q))$ determined by the structure map $L \to L((q))$ on the first factor and by $\iota$ restricted to $F_0$ on the second, so $c \otimes f \mapsto c\,\iota(f)$; by `baseChangeHom_mem` its image is contained in `laurentBaseChange L F₀`. Give `laurentBaseChange L F₀` the $L \otimes_{\mathbb{Q}} F_0$-algebra structure coming from $\beta$ corestricted to this intermediate field. The assertion is that `laurentBaseChange L F₀` is then a fraction ring of $L \otimes_{\mathbb{Q}} F_0$ in the sense of Mathlib's `IsFractionRing`.
--
--   This identifies the compositum $L\cdot F_0 \subseteq L((q))$ with the fraction field of $L \otimes_{\mathbb{Q}} F_0$, the standard description of a constant-field extension of a function field; for $L/\mathbb{Q}$ transcendental the map $\beta$ itself is not surjective, so passing to fractions is necessary. It is used in the geometric base change of the modular curve $X_1$, in particular in the comparison of the algebra of a chart with the compositum and in the resulting computations of genus and of dimensions of cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_GeometricBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.isFractionRing_tensorProduct_laurentBaseChange
    (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) :
    letI := ((ModularCurve.baseChangeHom L F₀).codRestrict (ModularCurve.laurentBaseChange L F₀).toSubalgebra
      (ModularCurve.baseChangeHom_mem L F₀)).toRingHom.toAlgebra
    IsFractionRing (L ⊗[ℚ] ↥F₀) ↥(ModularCurve.laurentBaseChange L F₀) := by sorry
