-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
-- name    : ModularCurve.exists_algEquiv_laurentBaseChange_cover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/a61da656-24d9-5f9d-a6a3-5750adeecac2
-- title:
--   Lifting automorphisms of F₀ to the compositum L· F₀
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, and let $\iota =$ [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) denote the ring homomorphism $\mathbb{Q}((q)) \to L((q))$ obtained by applying $\mathbb{Q} \to L$ coefficientwise to a Laurent series (formally, `LaurentSeries ℚ →+* LaurentSeries L` induced by `algebraMap ℚ L`). Let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$, and let [`ModularCurve.laurentBaseChange L F₀`](def/ModularCurve_LaurentCoeff.html#L103) be the intermediate field of $L \subseteq L((q))$ generated over $L$ by the image $\iota(F_0)$, i.e. the compositum $L\cdot \iota(F_0)$. Let $\sigma_0$ be a ring automorphism of $F_0$ (no $\mathbb{Q}$-linearity is imposed as a hypothesis). The assertion is that there exists an $L$-algebra automorphism $\tau$ of $L\cdot \iota(F_0)$ such that for every $y \in F_0$ the underlying Laurent series of $\tau$ evaluated at the element $\iota(y)$ of $L\cdot\iota(F_0)$ equals $\iota(\sigma_0(y))$; that is, $\tau \circ \iota = \iota \circ \sigma_0$ on $F_0$.
--
--   This is the base-change statement for automorphisms of a subfield of $\mathbb{Q}((q))$: automorphisms of $F_0$ extend to $L$-algebra automorphisms of the compositum $L\cdot F_0$ inside $L((q))$, the underlying reason being that $L$ and $\mathbb{Q}((q))$ are linearly disjoint over $\mathbb{Q}$ in $L((q))$. It is applied with $F_0$ a field of modular functions expanded in $q$, so as to transport involutions such as the Atkin–Lehner and Fricke involutions to the base-changed function field, and is used in that form by the results on Hecke and Atkin–Lehner endomorphisms of modular curves, for instance [`ModularCurve.XHDRLevel.algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic`](thm.html#ModularCurve.XHDRLevel.algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_algEquiv_laurentBaseChange_cover
    (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (σ₀ : ↥F₀ ≃+* ↥F₀) :
    ∃ τ : ↥(ModularCurve.laurentBaseChange L F₀) ≃ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀),
      ∀ y : ↥F₀,
        ((τ ⟨ModularCurve.coeffEmb L (y : LaurentSeries ℚ),
              ModularCurve.coeffEmb_mem_laurentBaseChange L y.2⟩ :
            ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L)
          = ModularCurve.coeffEmb L ((σ₀ y : ↥F₀) : LaurentSeries ℚ) := by sorry
