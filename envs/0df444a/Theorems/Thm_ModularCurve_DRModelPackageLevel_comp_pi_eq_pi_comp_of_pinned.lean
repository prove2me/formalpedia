-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_comp_pi_eq_pi_comp_of_pinned
-- name    : ModularCurve.DRModelPackageLevel.comp_pi_eq_pi_comp_of_pinned
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/b71f7635-0d88-5db5-8c4f-5ef33aec66aa
-- title:
--   Degeneracy maps commute with forgetting the Γ₀(q)-structure
-- statement:
--   Fix $N_0\ge 1$ and a prime $q$ with $q\nmid N_0$, and let $\mathfrak P$ be an inhabitant of `DRModelPackageLevel N₀ q hqN`; fix a prime $\ell$ with $q\nmid N_0\ell$ and an inhabitant $\mathfrak P'$ of `DRModelPackageLevel (N₀ * ℓ) q hqNℓ`. Write $R=$ `DRLevel.R q` and recall `DRLevel.toBase N q = IgusaScheme.igusaTo (N*q) q`, `DRLevel.toBase0 N q = IgusaScheme.igusaTo N q`. Let $\pi_1,\pi_2$ be morphisms over $\operatorname{Spec} R$ from `DRLevel.X (N₀*ℓ) q` to `DRLevel.X N₀ q` (elements of `SchemeHomOver`, i.e. morphisms commuting with the two copies of `toBase`), and let $\iota_1,\iota_2$ be $R$-algebra maps from the finite chart algebra `chartAlgFin (N₀*q) q` to `chartAlgFin (N₀*ℓ*q) q` such that, after coercion into the Laurent series field, $\iota_1$ preserves the $q$-expansion of every chart element while $\iota_2$ applies `qExpand ℚ ℓ` to it (the exponent-scaling ring map $f(q)\mapsto f(q^{\ell})$); assume $\pi_i$ is pinned by $\iota_i$, i.e. `ιFin (N₀*ℓ*q) q` followed by $\pi_i$ equals $\operatorname{Spec}(\iota_i)$ followed by `ιFin (N₀*q) q`. Let $\rho_1,\rho_2$ be morphisms over $\operatorname{Spec} R$ from `DRLevel.X0 (N₀*ℓ) q` to `DRLevel.X0 N₀ q`, pinned in the same way by $R$-algebra maps $\kappa_1,\kappa_2$ from `chartAlgFin N₀ q` to `chartAlgFin (N₀*ℓ) q` acting on $q$-expansions by the identity, respectively by `qExpand ℚ ℓ`. Then both squares commute: $\pi_i$ followed by the package morphism $\mathfrak P.\pi$ equals $\mathfrak P'.\pi$ followed by $\rho_i$, for $i=1,2$.
--
--   This is the functoriality of the two $\Gamma_0(\ell)$-degeneracy morphisms with respect to the morphism forgetting the $\Gamma_0(q)$-structure: the two towers $X_0(N_0\ell q)\to X_0(N_0 q)\to X_0(N_0)$ and $X_0(N_0\ell q)\to X_0(N_0\ell)\to X_0(N_0)$ agree at the level of Deligne–Rapoport models over $\mathbb Z_{(q)}$. It is used in the construction of a Hecke degeneracy pair, [`ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair`](thm.html#ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_comp_pi_eq_pi_comp_of_pinned.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.comp_pi_eq_pi_comp_of_pinned (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) (ℓ : ℕ) [Fact ℓ.Prime] (hqNℓ : ¬ q ∣ N₀ * ℓ)
    (𝔓' : DRModelPackageLevel (N₀ * ℓ) q hqNℓ)
    (π₁ π₂ : SchemeHomOver (DRLevel.toBase (N₀ * ℓ) q) (DRLevel.toBase N₀ q))
    (ι₁ ι₂ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q))
    (hι₁ : ∀ b, (((ι₁ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hι₂ : ∀ b, (((ι₂ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hπ₁ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₁.1 = Spec.map (CommRingCat.ofHom ι₁.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hπ₂ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₂.1 = Spec.map (CommRingCat.ofHom ι₂.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (ρ₁ ρ₂ : SchemeHomOver (DRLevel.toBase0 (N₀ * ℓ) q) (DRLevel.toBase0 N₀ q))
    (κ₁ κ₂ : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ) q))
    (hκ₁ : ∀ b, (((κ₁ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hκ₂ : ∀ b, (((κ₂ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ))) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hρ₁ : IgusaScheme.ιFin (N₀ * ℓ) q ≫ ρ₁.1 = Spec.map (CommRingCat.ofHom κ₁.toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (hρ₂ : IgusaScheme.ιFin (N₀ * ℓ) q ≫ ρ₂.1 = Spec.map (CommRingCat.ofHom κ₂.toRingHom) ≫ IgusaScheme.ιFin N₀ q) :
    π₁.1 ≫ 𝔓.π.1 = 𝔓'.π.1 ≫ ρ₁.1 ∧ π₂.1 ≫ 𝔓.π.1 = 𝔓'.π.1 ≫ ρ₂.1 := by sorry
