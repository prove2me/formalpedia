-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_crossingPt_mem_preimage_iotaFin
-- name    : ModularCurve.DRModelPackageLevel.crossingPt_mem_preimage_iotaFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/c94e4d58-c5cd-5e20-bb80-a6211b6faf80
-- title:
--   Crossing points lie over the j-finite chart
-- statement:
--   Let $N_0$ be a nonzero natural number and $q$ a prime with $q \nmid N_0$, and let $\mathfrak X$ be a `DRModelPackageLevel N₀ q hqN`, i.e. a package of Deligne–Rapoport data for the Igusa two-chart scheme `DRLevel.X N₀ q` over $\operatorname{Spec}$ of the ring `DRLevel.R q`, the structure morphism being `DRLevel.toBase N₀ q = IgusaScheme.igusaTo (N₀ * q) q`. Let $O$ be a commutative ring with a ring homomorphism $\rho_O \colon$ `DRLevel.R q` $\to O$, let $\kappa$ be an algebraically closed field of characteristic $q$, and let $\mathrm{to}\kappa \colon O \to \kappa$ be a ring homomorphism, so that $\mathrm{to}\kappa \circ \rho_O$ is a geometric point of the base in characteristic $q$. Let $n$ be a point of the fibre product of the two morphisms `𝔛.comp κ (toκ.comp ρO) 0` and `𝔛.comp κ (toκ.comp ρO) 1` attached to the package (the two branches of the geometric fibre, whose fibre product parametrises their crossings). The assertion is that the point `𝔛.crossingPt ρO toκ n` of `DRLevel.XO ρO`, namely the image of $n$ under the morphism on points of the first projection of that fibre product followed by `𝔛.comp κ (toκ.comp ρO) 0` followed by the base-change map `DRLevel.bcMap ρO toκ`, lies in the open subset obtained by pulling back, along the first projection of the fibre product of `DRLevel.toBase N₀ q` with $\operatorname{Spec}$ of $\rho_O$, the open image under `IgusaScheme.ιFin (N₀ * q) q` of the whole of its source.
--
--   This is the statement that a supersingular crossing point in a geometric characteristic-$q$ fibre of the Deligne–Rapoport model at level $\Gamma_0(N_0 q)$ lies over the $j$-finite chart of the Igusa two-chart presentation, so that local computations at such a point may be carried out in the finite chart algebra. It is used in the analysis of the local ring of the model at a crossing, specifically by [`ModularCurve.DRModelPackageLevel.exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing`](thm.html#ModularCurve.DRModelPackageLevel.exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_crossingPt_mem_preimage_iotaFin.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.crossingPt_mem_preimage_iotaFin
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1))) :
    𝔛.crossingPt ρO toκ n ∈
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) := by sorry
