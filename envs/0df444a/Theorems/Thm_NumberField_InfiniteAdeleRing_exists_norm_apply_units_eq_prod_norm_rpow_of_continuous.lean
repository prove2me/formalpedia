-- Prove2me | Theorems.Thm_NumberField_InfiniteAdeleRing_exists_norm_apply_units_eq_prod_norm_rpow_of_continuous
-- name    : NumberField.InfiniteAdeleRing.exists_norm_apply_units_eq_prod_norm_rpow_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/d5d9f1da-ee79-538c-91f5-5926293b76cc
-- title:
--   Modulus of a continuous character of K_∞^×
-- statement:
--   Let $K$ be a number field (a field with the `NumberField` structure), and let $K_\infty$ denote the infinite adele ring of $K$, that is, the product $\prod_{w \mid \infty} K_w$ of the completions of $K$ at its infinite places, indexed by `InfinitePlace K`. Let $\chi : K_\infty^\times \to \mathbb{C}^\times$ be a homomorphism of groups of units, and assume that the composite map $y \mapsto \chi(y)$, viewed as a map $K_\infty^\times \to \mathbb{C}$ by forgetting invertibility of the value, is continuous. The assertion is that there exists a family of real exponents $\sigma : \mathrm{InfinitePlace}(K) \to \mathbb{R}$ such that for every unit $y$ of $K_\infty$ one has $$\lVert \chi(y) \rVert = \prod_{w} \lVert y_w \rVert^{\sigma_w},$$ the product being over all infinite places $w$ of $K$, where $y_w$ is the $w$-component of the underlying element of $K_\infty$, $\lVert \cdot \rVert$ on the left is the complex absolute value, $\lVert \cdot \rVert$ on the right is the norm of the completion $K_w$, and the powers are real powers of nonnegative reals. No uniqueness of $\sigma$, and no information about $\chi$ beyond its modulus, is claimed.
--
--   This is the classical description of the modulus of a quasi-character of the archimedean part of the idele group: $|\chi|$ is trivial on the maximal compact subgroups of the factors $K_w^\times$ and is a real power of the absolute value on each positive ray. It is used in the analysis of archimedean components of idele class characters that enters the treatment of automorphic forms, being cited in the realisation of class sums in `AutomorphicForm`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfiniteAdeleRing_exists_norm_apply_units_eq_prod_norm_rpow_of_continuous.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.InfiniteAdeleRing.exists_norm_apply_units_eq_prod_norm_rpow_of_continuous
    (K : Type) [Field K] [NumberField K]
    (χ : (InfiniteAdeleRing K)ˣ →* ℂˣ) (hχ : Continuous fun y : (InfiniteAdeleRing K)ˣ => ((χ y : ℂˣ) : ℂ)) :
    ∃ σ : InfinitePlace K → ℝ, ∀ y : (InfiniteAdeleRing K)ˣ,
      ‖((χ y : ℂˣ) : ℂ)‖ = ∏ w : InfinitePlace K, ‖(y : InfiniteAdeleRing K) w‖ ^ σ w := by sorry
