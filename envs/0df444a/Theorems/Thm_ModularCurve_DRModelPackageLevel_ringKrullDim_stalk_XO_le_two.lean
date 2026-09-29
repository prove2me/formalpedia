-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_XO_le_two
-- name    : ModularCurve.DRModelPackageLevel.ringKrullDim_stalk_XO_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/1d93960a-cc3e-5620-afc3-97d10caeca4d
-- title:
--   Stalks of the base-changed level model have dimension at most two
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak{X}$ be a Deligne–Rapoport level package `DRModelPackageLevel N₀ q hqN` for the Igusa two-chart model `X N₀ q` over `Spec (DRLevel.R q)`. Such a package records that the structure morphism `toBase N₀ q`, namely `IgusaScheme.igusaTo (N₀ * q) q`, is proper, flat and locally of finite presentation, that `X N₀ q` is integral and that its ring of sections over every affine open is integrally closed; it further carries a curve model `Meta` of the modular function field of level $N_0 q$ over an algebraic closure of $\mathbb{Q}$, an isomorphism `eeta` of `Meta.C` with the pullback of `toBase` along that algebraic closure which is compatible with the two structure morphisms, Galois equivariance of the resulting correspondence between sections and places, a normalisation pinning the chart algebra against $q$-expansions of modular functions, smoothness of relative dimension one and geometric integrality of the generic fibre, sections $\varepsilon_\infty$ and $\varepsilon_0$ over the base, and further data, summarised here. Let $O$ be a discrete valuation ring which is a domain and let $\rho_O \colon \mathtt{DRLevel.R}\,q \to O$ be a ring homomorphism. The assertion is that for every point $z$ of the scheme `DRLevel.XO ρO` associated with $\rho_O$, the stalk of its structure sheaf at $z$ has Krull dimension at most $2$.
--
--   This is the two-dimensionality bound for the Deligne–Rapoport model of $X_0(N_0 q)$ after base change along $\rho_O$ to a discrete valuation ring: every local ring of the resulting arithmetic surface has dimension at most two. It is used in the construction of resolved model packages at level $(N_0, q)$ and in the local analysis of the crossing frame, where stalks are identified and invertibility of sections is checked.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_XO_le_two.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.ringKrullDim_stalk_XO_le_two
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (z : ↥(DRLevel.XO (N₀ := N₀) ρO)) :
    ringKrullDim ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk z) ≤ 2 := by sorry
