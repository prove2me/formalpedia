-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_heckeDegeneracyPair
-- name    : ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/2c3cc40a-f5ef-5767-903e-d53b8218ab1e
-- title:
--   Existence of q-expansion-pinned degeneracy pairs at level N₀ℓ
-- statement:
--   Let $N_0$ be a nonzero natural number, $q$ a prime with $q \nmid N_0$, and let $\mathfrak{P}$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ q hqN`; let $\ell$ be a prime with $q \nmid N_0\ell$ and let $\mathfrak{P}'$ be such a package at level $(N_0\ell, q)$. The assertion is that there exist: two morphisms $\pi_1,\pi_2$ from `DRLevel.X (N₀ * ℓ) q` to `DRLevel.X N₀ q` commuting with the structure morphisms `DRLevel.toBase` to $\operatorname{Spec}$ of `DRLevel.R q`, each finite and locally of finite presentation; $\mathbb{Z}$-algebra maps $\iota_1,\iota_2$ over `DRLevel.R q` between the finite chart algebras `IgusaScheme.chartAlgFin (N₀ * q) q` and `IgusaScheme.chartAlgFin (N₀ * ℓ * q) q`; two morphisms $\rho_1,\rho_2$ from `DRLevel.X0 (N₀ * ℓ) q` to `DRLevel.X0 N₀ q` over the base, finite and locally of finite presentation; algebra maps $\kappa_1,\kappa_2$ from `IgusaScheme.chartAlgFin N₀ q` to `IgusaScheme.chartAlgFin (N₀ * ℓ) q`; and an open $U$ of `DRLevel.X N₀ q`, such that: $\pi_1,\pi_2$ are surjective on points; on Laurent series $\iota_1$ and $\kappa_1$ act as the identity while $\iota_2$ and $\kappa_2$ act as `qExpand ℚ ℓ`, i.e. the substitution $f(q)\mapsto f(q^{\ell})$, via the inclusions of the chart algebras into `modularFunctionFieldFull`; each $\pi_i$ and $\rho_i$ is compatible with the corresponding chart immersion, in that `IgusaScheme.ιFin` followed by $\pi_i$ (resp. $\rho_i$) equals $\operatorname{Spec}$ of $\iota_i$ (resp. $\kappa_i$) followed by `IgusaScheme.ιFin`; each $\pi_i$ commutes with the morphisms $\mathfrak{P}'.w$ and $\mathfrak{P}.w$ carried by the packages, and intertwines the package morphisms $\mathfrak{P}'.\pi$ and $\mathfrak{P}.\pi$ with $\rho_i$, i.e. $\pi_i$ followed by $\mathfrak{P}.\pi$ equals $\mathfrak{P}'.\pi$ followed by $\rho_i$; both $\rho_i$ are flat with `finrank` equal to $\ell$ if $\ell \mid N_0$ and to $\ell+1$ otherwise at every point; and $U$ contains every point of `DRLevel.X N₀ q` whose stalk is a regular local ring, contains $\mathfrak{P}.\mathrm{smoothLocus}$, the restrictions of $\pi_1,\pi_2$ over $U$ are flat, and the `finrank` of $\pi_i$ at every point of $U$ is again $\ell$ or $\ell+1$ according as $\ell \mid N_0$ or not.
--
--   This is the unconditional existence of the pair of degeneracy maps underlying the Hecke correspondence at $\ell$ on the Deligne–Rapoport integral models of $X_0(N_0 q)$ and $X_0(N_0)$ over $\mathbb{Z}_{(q)}$, for every prime $\ell \neq q$, including the case $\ell \mid N_0$; the second map is pinned by the substitution $q \mapsto q^{\ell}$ on $q$-expansions rather than by a partial Atkin–Lehner involution. It is used by [`ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_eq_comp_of_ne`](thm.html#ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_eq_comp_of_ne) to identify the generic fibre of the pair with the Hecke correspondence on the geometric modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_heckeDegeneracyPair.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve.IgusaScheme ModularCurve.DRLevel
open ModularCurve
namespace ModularCurve.DRModelPackageLevel

theorem exists_heckeDegeneracyPair (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) (ℓ : ℕ) [Fact ℓ.Prime] (hqNℓ : ¬ q ∣ N₀ * ℓ)
    (𝔓' : DRModelPackageLevel (N₀ * ℓ) q hqNℓ) :
    ∃ (π₁ π₂ : SchemeHomOver (DRLevel.toBase (N₀ * ℓ) q) (DRLevel.toBase N₀ q))
      (_ : IsFinite π₁.1) (_ : IsFinite π₂.1) (_ : LocallyOfFinitePresentation π₁.1) (_ : LocallyOfFinitePresentation π₂.1)
      (ι₁ ι₂ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q))
      (ρ₁ ρ₂ : SchemeHomOver (DRLevel.toBase0 (N₀ * ℓ) q) (DRLevel.toBase0 N₀ q))
      (_ : IsFinite ρ₁.1) (_ : IsFinite ρ₂.1) (_ : LocallyOfFinitePresentation ρ₁.1) (_ : LocallyOfFinitePresentation ρ₂.1)
      (κ₁ κ₂ : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ) q))
      (U : (DRLevel.X N₀ q).Opens),

      Function.Surjective π₁.1.base ∧ Function.Surjective π₂.1.base ∧

      (∀ b, (((ι₁ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ)) ∧
      (∀ b, (((ι₂ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ)) ∧
      IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₁.1 = Spec.map (CommRingCat.ofHom ι₁.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q ∧
      IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₂.1 = Spec.map (CommRingCat.ofHom ι₂.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q ∧

      𝔓'.w.hom ≫ π₁.1 = π₁.1 ≫ 𝔓.w.hom ∧ 𝔓'.w.hom ≫ π₂.1 = π₂.1 ≫ 𝔓.w.hom ∧

      (∀ b, (((κ₁ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ)) ∧
      (∀ b, (((κ₂ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ))) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ)) ∧
      IgusaScheme.ιFin (N₀ * ℓ) q ≫ ρ₁.1 = Spec.map (CommRingCat.ofHom κ₁.toRingHom) ≫ IgusaScheme.ιFin N₀ q ∧
      IgusaScheme.ιFin (N₀ * ℓ) q ≫ ρ₂.1 = Spec.map (CommRingCat.ofHom κ₂.toRingHom) ≫ IgusaScheme.ιFin N₀ q ∧
      Flat ρ₁.1 ∧ Flat ρ₂.1 ∧ (∀ y, ρ₁.1.finrank y = (if ℓ ∣ N₀ then ℓ else ℓ + 1)) ∧ (∀ y, ρ₂.1.finrank y = (if ℓ ∣ N₀ then ℓ else ℓ + 1)) ∧

      π₁.1 ≫ 𝔓.π.1 = 𝔓'.π.1 ≫ ρ₁.1 ∧ π₂.1 ≫ 𝔓.π.1 = 𝔓'.π.1 ≫ ρ₂.1 ∧

      (∀ x : ↥(DRLevel.X N₀ q), IsRegularLocalRing ((DRLevel.X N₀ q).presheaf.stalk x) → x ∈ U) ∧ 𝔓.smoothLocus ≤ U ∧
      Flat (π₁.1 ∣_ U) ∧ Flat (π₂.1 ∣_ U) ∧
      (∀ y, y ∈ U → π₁.1.finrank y = (if ℓ ∣ N₀ then ℓ else ℓ + 1)) ∧ (∀ y, y ∈ U → π₂.1.finrank y = (if ℓ ∣ N₀ then ℓ else ℓ + 1)) := by sorry
