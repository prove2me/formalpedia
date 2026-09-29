-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_bcMap_apply_notMem_preimage_basicOpen
-- name    : ModularCurve.DRLevel.bcMap_apply_notMem_preimage_basicOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/46a8179f-d87d-546a-8d54-6412bd99fb6a
-- title:
--   Base-changed points of the level model lie over V(q)
-- statement:
--   Let $N_0$ be a nonzero natural number and $q$ a prime. Let $O$ be a commutative ring with a ring homomorphism $\rho_O \colon \mathrm{DRLevel.R}\,q \to O$ from the base ring of the level-$(N_0,q)$ model, let $\kappa$ be a commutative ring of characteristic $q$, and let $t \colon O \to \kappa$ be a ring homomorphism. Write $\mathfrak{X} \to \operatorname{Spec}(\mathrm{DRLevel.R}\,q)$ for the structure morphism `DRLevel.toBase N₀ q`, namely the Igusa two-chart model morphism `IgusaScheme.igusaTo (N₀ * q) q`. Then `DRLevel.fibre (t \circ \rho_O)` is the pullback of this morphism along $\operatorname{Spec}$ of $t \circ \rho_O$, and `DRLevel.XO ρO` is its pullback along $\operatorname{Spec} \rho_O$, with `DRLevel.XO.toBase ρO` the second projection to $\operatorname{Spec} O$; the morphism `DRLevel.bcMap ρO toκ` is the base-change map between them induced by the identity on $\mathfrak{X}$, by $\operatorname{Spec}$ of $t$, and by the identity on $\operatorname{Spec}(\mathrm{DRLevel.R}\,q)$. The assertion is that for every point $y$ of `DRLevel.fibre (t \circ \rho_O)`, the image of $y$ under the underlying continuous map of `DRLevel.bcMap ρO toκ` does not lie in the preimage, under the second projection to $\operatorname{Spec} O$, of the basic open set $D(q) \subseteq \operatorname{Spec} O$; equivalently, that image point lies over a prime of $O$ containing $q$.
--
--   A functoriality remark about the Deligne–Rapoport model of $X_0(N_0 q)$ over the base ring of the level-$(N_0,q)$ package: points coming from a characteristic-$q$ base change necessarily lie in the closed subscheme cut out by $q$. It is used in the analysis of the crossing points of the special fibre, for instance in [`ModularCurve.DRModelPackageLevel.eq_xi_of_ringKrullDim_stalk_le_one`](thm.html#ModularCurve.DRModelPackageLevel.eq_xi_of_ringKrullDim_stalk_le_one) and in the construction of a resolved model package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_bcMap_apply_notMem_preimage_basicOpen.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRLevel.bcMap_apply_notMem_preimage_basicOpen
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O) (κ : Type) [CommRing κ] [CharP κ q] (toκ : O →+* κ)
    (y : ↥(DRLevel.fibre (N₀ := N₀) (toκ.comp ρO))) :
    (DRLevel.bcMap ρO toκ).base y ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by sorry
