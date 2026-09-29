-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_mem_preimage_smoothLocus
-- name    : ModularCurve.DRModelPackage.baseChangeMap_genericPoint_mem_preimage_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/228f4a98-6d2a-58ed-bbe4-531c0b51b600
-- title:
--   Generic points of the two special-fibre components are smooth
-- statement:
--   Let $p$ be a prime, let $\mathfrak{X}$ be a Deligne–Rapoport package for the integral two-chart model `DRModel p` $=$ `TwoChartIntegralModel` $\mathbb{Z}$ of the full modular function field of level $p$ with its structure morphism `DRModel.toBase p` to $\operatorname{Spec}\mathbb{Z}$, let $O$ be a commutative ring, let $\kappa$ be an algebraically closed field of characteristic $p$, and let $t : O \to \kappa$ be a ring homomorphism. Write $\mathfrak{X}_O$ and $\mathfrak{X}_\kappa$ for the fibre products of `DRModel.toBase p` with $\operatorname{Spec}$ of $\mathbb{Z} \to O$, resp. $\mathbb{Z} \to \kappa$, and let `DRModel.baseChangeMap` $t : \mathfrak{X}_\kappa \to \mathfrak{X}_O$ be the map induced by the identity on `DRModel p` and $\operatorname{Spec} t$ on the base. Let $C$ be the underlying scheme of the curve model $\mathfrak{X}.\mathrm{ratModel}\ \kappa$ over $\kappa$ recorded in the package (integral, proper and smooth of relative dimension $1$ over $\kappa$), with its two morphisms $\mathfrak{X}.\mathrm{compInf}\ \kappa$, $\mathfrak{X}.\mathrm{compZero}\ \kappa : C \to \mathfrak{X}_\kappa$, and let $\eta$ be the generic point of $C$. Then the images of $\eta$ under both composites $C \to \mathfrak{X}_\kappa \to \mathfrak{X}_O$ lie in the preimage under the first projection $\mathfrak{X}_O \to$ `DRModel p` of the open subscheme $\mathfrak{X}.\mathrm{smoothLocus}$ of `DRModel p` recorded in the package.
--
--   This is the assertion that the generic points of the two components of the geometric special fibre at $p$ of the Deligne–Rapoport model of $X_0(p)$ are smooth points, hence distinct from the supersingular crossing points; after base change to an arbitrary $O$ the two resulting points of $\mathfrak{X}_O$ still lie over the smooth locus. It feeds the construction of the resolved model package and the computation of the branch ideals of the two components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_mem_preimage_smoothLocus.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRModelPackage.baseChangeMap_genericPoint_mem_preimage_smoothLocus
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) :
    (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ∈
        (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ 𝔛.smoothLocus ∧
    (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ∈
        (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ 𝔛.smoothLocus := by sorry
