-- Prove2me | Theorems.Thm_ModularCurve_exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq
-- name    : ModularCurve.exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/845729f6-5369-5f03-90bb-223ab3660cf1
-- title:
--   Transport of a p-torsion dlog datum along equal subfields
-- statement:
--   Let $K$ be a field, $p$ a natural number, and let $F_1, F_2$ be intermediate fields of the extension $K((q))/K$ (Laurent series over $K$) which are equal, $F_1 = F_2$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself and a principal ideal ring; divisors are the finitely supported $\mathbb{Z}$-valued functions on places, $\mathrm{Pic}^0$ is the group of degree-zero divisors modulo the principal ones, and `Pic0.torsion K F p` is its subgroup of elements killed by $p$. Suppose given an additive map $\delta_1$ from `Pic0.torsion K F₁ p` to $\Omega_{F_1/K}$ obeying the logarithmic-derivative recipe: whenever a degree-zero divisor $E$ represents the class $y$ and $g \in F_1$ is nonzero with $p\,E(v) = \operatorname{ord}_v(g)$ at every place $v$, then $\delta_1 y = g^{-1}\,\mathrm{d}g$. The conclusion asserts the existence of an additive isomorphism $\tau$ from `Pic0.torsion K F₁ p` to `Pic0.torsion K F₂ p` and an additive map $\delta_2$ from `Pic0.torsion K F₂ p` to $\Omega_{F_2/K}$ such that: the class of $\tau x$ in $\mathrm{Pic}^0(F_2)$ is the image of the class of $x$ under `Pic0.congr` for the $K$-algebra isomorphism `IntermediateField.equivOfEq hE`; $\delta_2$ obeys the same recipe over $F_2$; and for all $x$, `qExpansionDiffAlong F₂.val (δ₂ (τ x))` equals `qExpansionDiffAlong F₁.val (δ₁ x)`, where `qExpansionDiffAlong σ` denotes the $K$-linear map $\Omega_{F/K} \to K((q))$ sending $\mathrm{d}x$ to $\theta(\sigma x)$ and satisfying $f \cdot \omega \mapsto \sigma(f)\,\varphi(\omega)$ (taken to be zero if no such map exists), applied along the inclusions $F_i \hookrightarrow K((q))$.
--
--   This is a transport-of-structure step for Serre's $\delta = \mathrm{dlog}$ datum on the $p$-torsion of the Jacobian of a modular curve presented as an intermediate field of $K((q))$: it moves a map obeying the recipe, together with its $q$-expansion, across an equality of such subfields. It is used in the comparison of $q$-expansions of differentials with the Hecke operator $U_p$ and the Frobenius pushforward.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq
    (K : Type*) [Field K] (p : ℕ)
    {F₁ F₂ : IntermediateField K (LaurentSeries K)} (hE : F₁ = F₂)
    (δ₁ : Pic0.torsion K F₁ p →+ Ω[↥F₁⁄K])
    (hδ₁ : ∀ (y : Pic0.torsion K F₁ p) (E : Divisor.degZero (K := K) (F := ↥F₁)) (g : ↥F₁),
        Pic0.mk E = (y : Pic0 K F₁) → g ≠ 0 →
        (∀ v : Place K F₁, (p : ℤ) * (E : Divisor K F₁) v = v.ord g) →
        δ₁ y = g⁻¹ • KaehlerDifferential.D K (↥F₁) g) :
    ∃ (τ : Pic0.torsion K F₁ p ≃+ Pic0.torsion K F₂ p)
      (δ₂ : Pic0.torsion K F₂ p →+ Ω[↥F₂⁄K]),
      (∀ x : Pic0.torsion K F₁ p, ((τ x : Pic0.torsion K F₂ p) : Pic0 K F₂) =
        Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 K F₁)) ∧
      (∀ (y : Pic0.torsion K F₂ p) (E : Divisor.degZero (K := K) (F := ↥F₂)) (g : ↥F₂),
        Pic0.mk E = (y : Pic0 K F₂) → g ≠ 0 →
        (∀ v : Place K F₂, (p : ℤ) * (E : Divisor K F₂) v = v.ord g) →
        δ₂ y = g⁻¹ • KaehlerDifferential.D K (↥F₂) g) ∧
      (∀ x : Pic0.torsion K F₁ p,
        qExpansionDiffAlong F₂.val (δ₂ (τ x)) = qExpansionDiffAlong F₁.val (δ₁ x)) := by sorry
