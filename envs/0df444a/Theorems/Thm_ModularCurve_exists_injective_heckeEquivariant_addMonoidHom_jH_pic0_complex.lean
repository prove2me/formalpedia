-- Prove2me | Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex
-- name    : ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/51261eab-35f8-556e-bec1-5fa3b4b073aa
-- title:
--   Base change of J_H(M) to ℂ: injectivity, torsion, Hecke
-- statement:
--   Let $M$ be a nonzero natural number and $H$ a subgroup of $(\mathbb{Z}/M)^{\times}$. Write $F =$ `xHFunctionField M H` for the intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ attached to $X_H(M)$, $\bar{F} =$ `xHFunctionFieldBar M H` for the subfield of $\bar{\mathbb{Q}}((q))$ generated over $\bar{\mathbb{Q}}$ by the coefficientwise image of $F$, and $F_{\mathbb{C}} =$ `laurentBaseChange ℂ (xHFunctionField M H)` for the analogous subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$; here $J_H(M) = \mathrm{Pic}^0(\bar{\mathbb{Q}}, \bar{F})$ is the group of finitely supported $\mathbb{Z}$-valued divisors of degree zero on the places of $\bar{F}/\bar{\mathbb{Q}}$ modulo principal ones, and likewise for $\mathrm{Pic}^0(\mathbb{C}, F_{\mathbb{C}})$. The assertion is that there exist a ring homomorphism $\varphi : \bar{F} \to F_{\mathbb{C}}$ and an additive homomorphism $\iota : J_H(M) \to \mathrm{Pic}^0(\mathbb{C}, F_{\mathbb{C}})$ such that: (i) $\varphi$ is application of [`complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ`](def/GaloisRep_ComplexConjugation.html#L14) to the coefficients of a Laurent series, i.e. $\varphi y =$ `coeffMap` of that embedding applied to $y$; (ii) $\iota$ is injective; (iii) every element of $\mathrm{Pic}^0(\mathbb{C}, F_{\mathbb{C}})$ of finite additive order lies in the range of $\iota$; (iv) for every nonzero $\ell$ for which the input package [`ModularCurve.HeckeInputsHAlong`](def/ModularCurve_XHHeckeOperator.html#L186) (existence of the defined $\beta$-map, integrality of the two degeneracy maps over the base, the principal-divisor property for the level-$M\ell$ field, finiteness along $\alpha$, the fundamental identity along $\beta$ and the norm formula along $\alpha$) holds both over $\bar{\mathbb{Q}}$ and over $\mathbb{C}$, the map $\iota$ intertwines the two operators `heckeOperatorHAlong` at $\ell$; (v) for every pair $g$ of a ring automorphism of $\bar{F}$ and one of $\bar{\mathbb{Q}}$ compatible with the inclusion of constants, and every such pair $g'$ for $F_{\mathbb{C}}/\mathbb{C}$, if $g' \cdot \varphi y = \varphi(g \cdot y)$ for all $y$ then $\iota(g \cdot x) = g' \cdot \iota x$ for all $x$; and (vi) every $\bar{\mathbb{Q}}$-algebra automorphism $\sigma$ of $\bar{F}$ admits a $\mathbb{C}$-algebra automorphism $\sigma'$ of $F_{\mathbb{C}}$ with $\sigma' \circ \varphi = \varphi \circ \sigma$.
--
--   This is the conorm map along the constant-field extension $\bar{\mathbb{Q}}F \subseteq \mathbb{C}F$ of the function field of $X_H(M)$: it identifies $J_H(M)(\bar{\mathbb{Q}})$ with the torsion subgroup of the degree-zero divisor class group over $\mathbb{C}$, compatibly with Hecke operators and with semilinear automorphisms. It is used to transport the Jacobian of $X_H(M)$ to the complex-analytic side, and is cited by the results presenting $J_H(M)$ inside a quotient by a period lattice, in Hecke-equivariant form and compatibly with complex conjugation and the level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex.lean

import Mathlib
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_GaloisRep_ComplexConjugation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ (φ : ↥(ModularCurve.xHFunctionFieldBar M H) →+*
          ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
      (ι : ModularCurve.JH M H →+
          AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))),
      (∀ y : ↥(ModularCurve.xHFunctionFieldBar M H),
        ((φ y : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))) : LaurentSeries ℂ) =
          ModularCurve.coeffMap (complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom
            (y : LaurentSeries (AlgebraicClosure ℚ))) ∧
      Function.Injective ι ∧
      (∀ z, IsOfFinAddOrder z → z ∈ ι.range) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ],
        ModularCurve.HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ →
        ModularCurve.HeckeInputsHAlong ℂ M H ℓ →
        ∀ x : ModularCurve.JH M H,
          ι (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ x) =
            ModularCurve.heckeOperatorHAlong ℂ M H ℓ (ι x)) ∧
      (∀ (g : AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
        (g' : AlgebraicCurve.SemilinearAut ℂ
          ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))),
        (∀ y : ↥(ModularCurve.xHFunctionFieldBar M H), g' • φ y = φ (g • y)) →
        ∀ x : ModularCurve.JH M H, ι (g • x) = g' • ι x) ∧
      ∀ σ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H),
        ∃ σ' : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ≃ₐ[ℂ]
            ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)),
          ∀ y : ↥(ModularCurve.xHFunctionFieldBar M H), σ' (φ y) = φ (σ y) := by sorry
