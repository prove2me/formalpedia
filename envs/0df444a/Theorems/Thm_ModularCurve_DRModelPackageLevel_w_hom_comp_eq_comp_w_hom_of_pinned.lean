-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_w_hom_comp_eq_comp_w_hom_of_pinned
-- name    : ModularCurve.DRModelPackageLevel.w_hom_comp_eq_comp_w_hom_of_pinned
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/106819ad-1855-5a15-8d66-fae2d510811c
-- title:
--   Chart-pinned degeneracy maps commute with w_q
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$ with $q \nmid N_0$, and a prime $\ell$ with $q \nmid N_0\ell$. Let $\mathfrak{P}$ be a `DRModelPackageLevel N₀ q hqN`, so a bundle of properties for the structure morphism `DRLevel.toBase N₀ q` of the Igusa-type model $X(N_0,q)$ over $\operatorname{Spec}$ of the base ring `DRLevel.R q`, and let $\mathfrak{P}'$ be such a bundle at level $N_0\ell$. Let $\pi_1,\pi_2$ be morphisms $X(N_0\ell,q) \to X(N_0,q)$ commuting with the two structure morphisms to the base (elements of the subtype `SchemeHomOver`). Let $\iota_1,\iota_2$ be `DRLevel.R q`-algebra maps from the chart algebra `IgusaScheme.chartAlgFin (N₀ * q) q`, the subalgebra of elements of the modular function field of level $N_0q$ integral over the base ring adjoined $j$, to the corresponding chart algebra at level $N_0\ell q$, and assume that on Laurent series $\iota_1$ preserves the $q$-expansion of every element, while $\iota_2$ sends it to its image under `qExpand ℚ ℓ`, the substitution multiplying all exponents by $\ell$. Assume furthermore that the chart immersion `IgusaScheme.ιFin (N₀ * ℓ * q) q` followed by $\pi_i$ equals $\operatorname{Spec}(\iota_i)$ followed by `IgusaScheme.ιFin (N₀ * q) q`, for $i=1,2$. Then the underlying morphism of $\mathfrak{P}'.w$ followed by $\pi_i$ equals $\pi_i$ followed by the underlying morphism of $\mathfrak{P}.w$, for both $i=1$ and $i=2$.
--
--   This is the commutation of the partial Atkin–Lehner involution $w_q$ with the two degeneracy (level-raising) maps $X_0(N_0\ell q) \rightrightarrows X_0(N_0 q)$ associated with the auxiliary prime $\ell \ne q$, in the form needed for the integral Deligne–Rapoport models over $\mathbb{Z}_{(q)}$. It is used by [`ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair`](thm.html#ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair) to produce a pair of degeneracy morphisms compatible with $w_q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_w_hom_comp_eq_comp_w_hom_of_pinned.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve.IgusaScheme ModularCurve.DRLevel
open ModularCurve

theorem ModularCurve.DRModelPackageLevel.w_hom_comp_eq_comp_w_hom_of_pinned (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) (ℓ : ℕ) [Fact ℓ.Prime] (hqNℓ : ¬ q ∣ N₀ * ℓ)
    (𝔓' : DRModelPackageLevel (N₀ * ℓ) q hqNℓ)
    (π₁ π₂ : SchemeHomOver (DRLevel.toBase (N₀ * ℓ) q) (DRLevel.toBase N₀ q))
    (ι₁ ι₂ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q))
    (hι₁ : ∀ b, (((ι₁ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hι₂ : ∀ b, (((ι₂ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hπ₁ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₁.1 = Spec.map (CommRingCat.ofHom ι₁.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hπ₂ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₂.1 = Spec.map (CommRingCat.ofHom ι₂.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q) :
    𝔓'.w.hom ≫ π₁.1 = π₁.1 ≫ 𝔓.w.hom ∧ 𝔓'.w.hom ≫ π₂.1 = π₂.1 ≫ 𝔓.w.hom := by sorry
