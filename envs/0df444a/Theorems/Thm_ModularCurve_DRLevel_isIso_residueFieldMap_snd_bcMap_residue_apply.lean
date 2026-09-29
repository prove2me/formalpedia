-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_isIso_residueFieldMap_snd_bcMap_residue_apply
-- name    : ModularCurve.DRLevel.isIso_residueFieldMap_snd_bcMap_residue_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/98c9e36d-f9cb-5339-aadc-c1a322478bc5
-- title:
--   Residue field of a k_O-rational point of the closed fibre
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$, and let $O$ be a commutative local ring with a ring homomorphism $\rho_O \colon R_q \to O$ from the base ring `DRLevel.R q` of the level-$(N_0,q)$ model. Write $k_O = O/\mathfrak m_O$ for the residue field and $O \to k_O$ for the residue map. Let `DRLevel.fibre ((residue O).comp ρO)` be the fibre product of the structure morphism `DRLevel.toBase N₀ q` with $\operatorname{Spec}$ of the composite $R_q \to O \to k_O$, and let `DRLevel.XO ρO` be the corresponding scheme over $O$, its structure morphism $\pi =$ `DRLevel.XO.toBase ρO` being the second projection to $\operatorname{Spec} O$; let $\iota =$ `DRLevel.bcMap ρO (residue O)` be the morphism of fibre products induced by the identity on `DRLevel.toBase N₀ q` and by $\operatorname{Spec}$ of $O \to k_O$. Assume given $s \colon \operatorname{Spec} k_O \to$ `DRLevel.fibre ((residue O).comp ρO)` with $s$ followed by the second projection equal to the identity of $\operatorname{Spec} k_O$. Let $x = \iota(s(\mathrm{pt}))$, the image under $\iota$ of the image under $s$ of the closed point of $\operatorname{Spec} k_O$. Then the induced map of residue fields $\kappa(\pi(x)) \to \kappa(x)$ is an isomorphism.
--
--   The statement records that a $k_O$-valued section of the closed fibre of the base change of the Deligne–Rapoport level model along $\rho_O \colon R_q \to O$ gives a point of the total space whose residue field coincides with $k_O = \kappa(\mathfrak m_O)$, i.e. a $k_O$-rational point in the strict sense. It is purely formal, using no datum of the model package, and feeds into the injectivity statement [`ModularCurve.DRModelPackageLevel.injective_crossingPt_of_exists_section`](thm.html#ModularCurve.DRModelPackageLevel.injective_crossingPt_of_exists_section) for crossing points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_isIso_residueFieldMap_snd_bcMap_residue_apply.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRLevel.isIso_residueFieldMap_snd_bcMap_residue_apply
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
    (s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO))
    (hs : s ≫ pullback.snd _ _ = 𝟙 _) :
    IsIso ((DRLevel.XO.toBase (N₀ := N₀) ρO).residueFieldMap
      ((DRLevel.bcMap ρO (IsLocalRing.residue O)).base
        (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))))) := by sorry
