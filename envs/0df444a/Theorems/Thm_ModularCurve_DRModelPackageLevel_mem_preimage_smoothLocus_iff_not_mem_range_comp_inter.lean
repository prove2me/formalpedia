-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
-- name    : ModularCurve.DRModelPackageLevel.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/1b9ed9ab-e64d-585a-8612-fc1d0c7c1c92
-- title:
--   Smooth locus meets the geometric fibre off the crossings
-- statement:
--   Fix a positive integer $N_0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel N₀ p hpN₀`, i.e. a bundle of data and properties attached to the scheme `X N₀ p` over $\operatorname{Spec}(R\,p)$ with structural map `DRLevel.toBase N₀ p` (the Igusa-type morphism `igusaTo (N₀ * p) p`): properness, flatness, integrality and local finite presentation of that morphism, normality of its affine charts, a curve model `Meta` over $\overline{\mathbf Q}$ identified with the geometric generic fibre compatibly with the Galois action and with the pinning of the Igusa charts, smoothness of relative dimension $1$ and geometric integrality of the rational generic fibre, sections `εinf`, `εzero` over the base, and the further data used below, among them an open subscheme `𝔓.smoothLocus` of `X N₀ p` and, for each algebraically closed residue field, two morphisms into the corresponding fibre. Let $\kappa$ be an algebraically closed field of characteristic $p$, let $\mathrm{to}\kappa : R\,p \to \kappa$ be a ring homomorphism, and let $y$ be a point of `DRLevel.fibre toκ`, the pullback of `DRLevel.toBase N₀ p` along $\operatorname{Spec}(\mathrm{to}\kappa)$. Then $y$ lies in the preimage of `𝔓.smoothLocus` under the first projection of that pullback if and only if it is not the case that $y$ lies simultaneously in the image of `(𝔓.comp κ toκ 0).base` and in the image of `(𝔓.comp κ toκ 1).base`.
--
--   This is the level-$N_0p$ form of the statement that the Deligne–Rapoport model of $X_0(N_0p)$ is smooth over the base away from the crossing points of the two components of its geometric special fibre, each component being a copy of the level-$N_0$ fibre. It is the geometric input for the local analysis of the model at $p$, and is cited in the construction of resolved model packages and in the computation of the branch ideals of the sections `εinf` and `εzero`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R p →+* κ)
    (y : ↥(DRLevel.fibre (N₀ := N₀) toκ)) :
    y ∈ (pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus) ↔
      ¬ (y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∈ Set.range (𝔓.comp κ toκ 1).base) := by sorry
