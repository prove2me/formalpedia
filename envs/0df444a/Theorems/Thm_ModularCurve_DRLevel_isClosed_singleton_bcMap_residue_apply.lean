-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_isClosed_singleton_bcMap_residue_apply
-- name    : ModularCurve.DRLevel.isClosed_singleton_bcMap_residue_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/3aa4b540-ddda-54f2-b3b1-f0d9ac71ea5c
-- title:
--   Image of a residue-field section is a closed point
-- statement:
--   Fix natural numbers $N_0$ and $q$ with $N_0 \neq 0$ and $q$ prime, and assume the structure morphism `DRLevel.toBase N₀ q` of the level-$N_0q$ Igusa scheme `DRLevel.X N₀ q` over $\operatorname{Spec}$ `DRLevel.R q` is separated. Let $O$ be a commutative local ring and $\rho_O \colon$ `DRLevel.R q` $\to O$ a ring homomorphism, and write $k =$ `IsLocalRing.ResidueField O` with residue map $O \to k$. Let $s$ be a morphism of schemes from $\operatorname{Spec} k$ to `DRLevel.fibre` of the composite `DRLevel.R q` $\to O \to k$, that is, to the fibre product of `DRLevel.toBase N₀ q` with $\operatorname{Spec}$ of that composite, and assume $s$ is a section of the projection to $\operatorname{Spec} k$, i.e. $s$ followed by `pullback.snd` is the identity. The morphism `DRLevel.bcMap ρO (IsLocalRing.residue O)` is the base-change morphism from this fibre to `DRLevel.XO ρO`, the fibre product of `DRLevel.toBase N₀ q` with $\operatorname{Spec} \rho_O$, given by the identity on the Igusa scheme factor and $\operatorname{Spec}$ of the residue map on the base. The conclusion is that the image under the underlying continuous map of `DRLevel.bcMap ρO (IsLocalRing.residue O)` of the point $s(\mathrm{pt})$, where $\mathrm{pt}$ is the closed point of $\operatorname{Spec} k$, is a closed singleton in the topological space of `DRLevel.XO ρO`.
--
--   This is the standard fact that a section of a separated morphism is a closed immersion, applied to the closed fibre of the Igusa scheme of level $N_0q$ over a local base: a $k$-rational point of the closed fibre gives a closed point of the model over $O$. It is used in the construction of resolved Deligne–Rapoport model packages at level $N_0q$, where closed points of the model over $O$ must be produced from points of the closed fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_isClosed_singleton_bcMap_residue_apply.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRLevel.isClosed_singleton_bcMap_residue_apply
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] [IsSeparated (DRLevel.toBase N₀ q)]
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
    (s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO))
    (hs : s ≫ pullback.snd _ _ = 𝟙 _) :
    IsClosed ({(DRLevel.bcMap ρO (IsLocalRing.residue O)).base
        (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)))} :
      Set ↥(DRLevel.XO (N₀ := N₀) ρO)) := by sorry
