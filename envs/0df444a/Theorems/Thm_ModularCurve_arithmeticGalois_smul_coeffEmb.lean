-- Prove2me | Theorems.Thm_ModularCurve_arithmeticGalois_smul_coeffEmb
-- name    : ModularCurve.arithmeticGalois_smul_coeffEmb
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/9ec5bcd8-8549-582f-bfe9-845509572068
-- title:
--   Arithmetic Galois action fixes ι_L(F₀) pointwise
-- statement:
--   Let $L$ be a field equipped with a $\mathbb Q$-algebra structure, let $F_0$ be an intermediate field of $\mathbb Q((q))/\mathbb Q$ (an `IntermediateField ℚ (LaurentSeries ℚ)`), let $\sigma$ be a $\mathbb Q$-algebra automorphism of $L$, and let $x$ be a Laurent series over $\mathbb Q$ with $x \in F_0$. Write $\iota_L =$ `coeffEmb L` for the coefficientwise ring homomorphism $\mathbb Q((q)) \to L((q))$ induced by $\operatorname{algebraMap} \mathbb Q L$, and `laurentBaseChange L F₀` for the intermediate field of $L((q))/L$ generated over $L$ by the image $\iota_L(F_0)$; by `coeffEmb_mem_laurentBaseChange`, $\iota_L(x)$ is an element of this compositum. The element `arithmeticGalois F₀ σ` is the pair consisting of the coefficientwise ring automorphism $\operatorname{coeffMap} \sigma$ of `laurentBaseChange L F₀` together with $\sigma$ itself on $L$, viewed as a member of the group `SemilinearAut L (laurentBaseChange L F₀)` of pairs of ring automorphisms compatible with the structure map $L \to L((q))$. The assertion is that this semilinear automorphism acts trivially on $\iota_L(x)$: $\operatorname{arithmeticGalois} F_0\,\sigma \bullet \iota_L(x) = \iota_L(x)$ as elements of `laurentBaseChange L F₀`.
--
--   This records that the coefficientwise ("arithmetic") Galois action on the base-changed Laurent-series field is trivial on the image of the rational subfield $F_0$, i.e. that the generators of the compositum are defined over $\mathbb Q$. It is used repeatedly in the study of the Galois action on the base-changed modular function field and its degree-zero Picard group, for instance in the computations of Frobenius and inertia at the special places of the fibre models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_arithmeticGalois_smul_coeffEmb.lean

import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.arithmeticGalois_smul_coeffEmb {L : Type*} [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (σ : L ≃ₐ[ℚ] L) {x : LaurentSeries ℚ} (hx : x ∈ F₀) : ModularCurve.arithmeticGalois F₀ σ • (⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ : ModularCurve.laurentBaseChange L F₀) = ⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ := by sorry
