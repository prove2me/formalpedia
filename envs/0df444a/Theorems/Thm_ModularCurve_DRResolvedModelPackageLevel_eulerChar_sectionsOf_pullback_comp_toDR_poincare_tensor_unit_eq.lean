-- Prove2me | Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_comp_toDR_poincare_tensor_unit_eq
-- name    : ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_comp_toDR_poincare_tensor_unit_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7270facf-4b12-5c52-a092-c5fe0e4a4a51
-- title:
--   Euler characteristic of the Poincaré pullback on a component
-- statement:
--   Fix a positive integer $N₀$ and a prime $p$ with $p \nmid N₀$, a model package $𝔓 : \mathrm{DRModelPackageLevel}\ N₀\ p$ for the structure morphism `DRLevel.toBase N₀ p` over the ring `DRLevel.R p`, and a relative $\mathrm{Pic}^0$ designation $D$ for that morphism, i.e. a scheme with a morphism `D.toBase` to $\operatorname{Spec}$ `DRLevel.R p` and a section `D.zeroSection`. Let $hD$ witness that $D$ represents the subfunctor of rigidified line bundles cut out by `algEquivZeroCut`: it provides a rigidified line bundle `hD.poincare` over `D.toBase` lying in that cut, a universal property, and the triviality of its restriction along the zero section; the cut consists of those rigidified bundles $M$ such that for every algebraically closed field $k$ and every $k$-point of the base the pullback of $M.L$ to the corresponding fibre is `IsAlgEquivZero`. Let $O$ be a commutative ring with a ring homomorphism $ρO$ from `DRLevel.R p`, let $κ$ be an algebraically closed field of characteristic $p$ with a ring homomorphism $toκ : O \to κ$, and let $𝔛reg$ be a resolved model package for $𝔓$ over $(O, ρO, κ, toκ)$. Let $z$ be a morphism $\operatorname{Spec} O \to D.P$ whose composite with `D.toBase` is $\operatorname{Spec}(ρO)$, let $w$ be an index in `X0MqComponents 𝔛reg.width`, so that `(𝔛reg.comp w).subscheme` is the corresponding closed subscheme of the resolved model with closed immersion `subschemeι`, let $y$ be a proper morphism from that subscheme to $\operatorname{Spec} κ$ whose composite with $\operatorname{Spec}(toκ)$ equals `subschemeι` followed by `𝔛reg.toBase`, and let $𝒲$ be a cover of the subscheme by two affine opens with affine intersection. Write $\mathcal L$ for the pullback of `(hD.poincare.pullbackAlong z).L` along `subschemeι` followed by `𝔛reg.toDR`. Then the two-chart Čech Euler characteristic over $κ$, namely $\dim_κ H^0 - \dim_κ H^1$ of the complex $(M_0 \times M_1 \to M_{01})$ of sections associated with $𝒲$ and $y$, is the same for $\mathcal L \otimes \mathcal O$ and for the monoidal unit $\mathcal O$ of the category of modules on the subscheme.
--
--   This is the statement that a line bundle lying in the algebraically-equivalent-to-zero cut of the relative Picard functor has, after restriction to any single component of the special fibre of the resolved model of $X_0(N_0p)$, the same Euler characteristic as the structure sheaf; it is the component-degree input to the multidegree computation, and is cited by [`ModularCurve.DRResolvedModelPackageLevel.sum_single_add_intersectionAlpha_eq_zero_of_pullback_toDR_iso`](thm.html#ModularCurve.DRResolvedModelPackageLevel.sum_single_add_intersectionAlpha_eq_zero_of_pullback_toDR_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_comp_toDR_poincare_tensor_unit_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian ModularCurve MazurRapoportAppendix
open scoped BigOperators

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_comp_toDR_poincare_tensor_unit_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (D : RelativePic0Designation (DRLevel.R p) (DRLevel.toBase N₀ p))
    (hD : RepresentsRelSubPic (DRLevel.toBase N₀ p) 𝔓.εinf (algEquivZeroCut (DRLevel.toBase N₀ p) 𝔓.εinf) D)
    (O : Type) [CommRing O] (ρO : DRLevel.R p →+* O)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase)
    (w : X0MqComponents 𝔛reg.width)
    (y : (𝔛reg.comp w).subscheme ⟶ Spec (CommRingCat.of κ))
    (hy : y ≫ Spec.map (CommRingCat.ofHom toκ) = (𝔛reg.comp w).subschemeι ≫ 𝔛reg.toBase) [IsProper y]
    (𝒲 : ((𝔛reg.comp w).subscheme).TwoAffineOpenCover) :
    (Module.finrank κ (𝒲.sectionsOf y ((Scheme.Modules.pullback ((𝔛reg.comp w).subschemeι ≫ 𝔛reg.toDR)).obj (hD.poincare.pullbackAlong z).L ⊗ 𝟙_ ((𝔛reg.comp w).subscheme).Modules)).H0 : ℤ)
      - Module.finrank κ (𝒲.sectionsOf y ((Scheme.Modules.pullback ((𝔛reg.comp w).subschemeι ≫ 𝔛reg.toDR)).obj (hD.poincare.pullbackAlong z).L ⊗ 𝟙_ ((𝔛reg.comp w).subscheme).Modules)).H1
    = (Module.finrank κ (𝒲.sectionsOf y (𝟙_ ((𝔛reg.comp w).subscheme).Modules)).H0 : ℤ)
      - Module.finrank κ (𝒲.sectionsOf y (𝟙_ ((𝔛reg.comp w).subscheme).Modules)).H1 := by sorry
