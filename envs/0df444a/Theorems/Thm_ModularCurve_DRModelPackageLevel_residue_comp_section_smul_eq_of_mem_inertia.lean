-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_residue_comp_section_smul_eq_of_mem_inertia
-- name    : ModularCurve.DRModelPackageLevel.residue_comp_section_smul_eq_of_mem_inertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/76e27f6c-4ab0-528e-b043-78c5c0b038a2
-- title:
--   Inertia fixes the reduction of the section attached to a place
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, assume $p \nmid N_0$, and let $\mathfrak{P}$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀`: a structure carrying the Igusa-type scheme $X$ of level $N_0p$ with its structure morphism `toBase N₀ p` to $\operatorname{Spec}(R_p)$ (proper, flat, integral, locally of finite presentation, with integrally closed sections on affine opens), a curve model $\mathfrak{P}.\mathrm{Meta}$ of the function field `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbb{Q}}$, an isomorphism $\mathfrak{P}.\mathrm{eeta}$ of its curve onto the base change of `toBase N₀ p` along $R_p \to \overline{\mathbb{Q}}$ compatible with the structure maps, the Galois-equivariance field `hgal` relating translation of $\overline{\mathbb{Q}}$-points by field automorphisms to the action on places, and further data including the sections $\varepsilon_\infty, \varepsilon_0$; properness of `toBase N₀ p` is additionally assumed as an instance. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ and $\rho : R_p \to A$ a ring homomorphism whose composition with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R_p \to \overline{\mathbb{Q}}$. The assertion is: for every $\sigma$ in `A.inertiaSubgroupIn ℚ`, the image in $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $A$ over $\mathbb{Q}$; for every place $V$ of `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbb{Q}}$, that is, a valuation subring of that field containing the image of $\overline{\mathbb{Q}}$, proper and a principal ideal ring; and for all sections $s, s'$ of `toBase N₀ p` over $\operatorname{Spec}(\rho)$ (morphisms $\operatorname{Spec}(A) \to X$ whose composite with `toBase N₀ p` is $\operatorname{Spec}(\rho)$) such that the restriction of $s$ along $\operatorname{Spec}(A \hookrightarrow \overline{\mathbb{Q}})$ is the $\overline{\mathbb{Q}}$-point $(\mathfrak{P}.\mathrm{Meta}.\mathrm{pointEquivPlace})^{-1}(V)$ followed by $\mathfrak{P}.\mathrm{eeta}$ and the first pullback projection, and the corresponding restriction of $s'$ is the point attached in the same way to `arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • V`, one has that $\operatorname{Spec}$ of the residue map $A \to A/\mathfrak{m}_A$ followed by $s'$ equals $\operatorname{Spec}$ of the residue map followed by $s$.
--
--   This is the statement that inertia acts trivially on the reduction of a point: two places of the modular function field differing by an element of the inertia group of $A$ give $A$-valued sections of the Deligne–Rapoport model with the same special fibre. It is used in the lemmas on extension of differences of cusps and of Hecke translates to places, `extendsToPlace_pts_mk_smul_single_sub_single_of_not_mem_range_comp_inter` and `extendsToPlace_pts_smul_sub`, and rests on the uniqueness of sections with prescribed generic point supplied by `existsUnique_section_comp_eq_pointEquivPlace_symm`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_residue_comp_section_smul_eq_of_mem_inertia.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.residue_comp_section_smul_eq_of_mem_inertia
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))
        (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
        (_hs : Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
          ((𝔓.Meta.pointEquivPlace).symm V).1 ≫ 𝔓.eeta ≫
            pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))))
        (s' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
        (_hs' : Spec.map (CommRingCat.ofHom A.subtype) ≫ s'.1 =
          ((𝔓.Meta.pointEquivPlace).symm (arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • V)).1 ≫ 𝔓.eeta ≫
            pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ))))),
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s'.1 =
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1 := by sorry
