-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_extendsToPlace_pts_add
-- name    : ModularCurve.DRModelPackageLevel.extendsToPlace_pts_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/81305269-eb82-5afc-bdca-d6678e9db75f
-- title:
--   Closure under addition of points extending to a place
-- statement:
--   Fix $N_0\ge 1$ and a prime $p$ with $p\nmid N_0$, and a package $\mathfrak P$ of type `DRModelPackageLevel N₀ p hpN₀` for the proper flat model `toBase N₀ p : X N₀ p ⟶ Spec (R p)` (carrying normality of affine charts, a `CurveModel` $\mathfrak P.\mathrm{Meta}$ over $\overline{\mathbb Q}$ for the field `modularFunctionFieldBar (N₀ * p)` identified by `eeta` with the geometric generic fibre, Galois compatibility of places, smoothness and geometric integrality of the generic fibre, and sections `εinf`, `εzero`), together with properness of `toBase N₀ p`. Let $D$ be a `RelativePic0Designation (R p) (toBase N₀ p)`, i.e. a scheme `D.P` over $\operatorname{Spec}(R p)$ with a section `D.zeroSection`, and let `hD` witness that $D$ represents the functor of line bundles on `toBase N₀ p` rigidified along `𝔓.εinf` and fibrewise algebraically trivial (`algEquivZeroCut`): a Poincaré bundle in the class, a universal property, and triviality along the zero section. Further data are assumed and summarised here: the corresponding representability `hDQ` over $\mathbb Q$ with the comparison `hPQ` of Poincaré bundles; an Abel–Jacobi morphism `ajQ` over $\mathbb Q$ with `hajQε`, `hajQ` computing pullbacks of the Poincaré bundle as $\mathcal L(x)\otimes\mathcal I(\infty)$; a comparison morphism `kQ` of the two base changes with `hkQ₁`, `hkQ₂`; the induced $\overline{\mathbb Q}$-level Abel–Jacobi map `ajbar` with its cusp point `εbar` and the relations `hajbar`, `hajbar_over`, `hεbar`, `hεbar_aj`; and a bijection `pts` from `JZero (N₀ * p)` to the $\overline{\mathbb Q}$-points of `D.toBase` over `genPt p` which is additive for the relative group law coming from `hD` (`hpts_add`), Galois-equivariant (`hpts_galois`) and Abel–Jacobi compatible (`hpts_aj`). Finally let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, and $\rho : R p \to A$ a ring homomorphism whose composite with the inclusion $A\hookrightarrow\overline{\mathbb Q}$ is the structure map. The conclusion: for all $x,y$ in `JZero (N₀ * p)`, if `pts x` and `pts y` each factor as the canonical $\overline{\mathbb Q}$-point `barPt A` of $\operatorname{Spec} A$ followed by an $A$-point of `D.P` over $\operatorname{Spec}\rho$, then so does `pts (x + y)`.
--
--   This is the additivity half of the statement that the points of $J_0(N_0p)(\overline{\mathbb Q})$ whose associated points of the relative $\mathrm{Pic}^0$-scheme of the Deligne–Rapoport model extend over a place $A$ above $p$ form a subgroup. It is used by [`ModularCurve.DRModelPackageLevel.extendsToPlace_pts_smul_sub`](thm.html#ModularCurve.DRModelPackageLevel.extendsToPlace_pts_smul_sub).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_extendsToPlace_pts_add.lean

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

theorem ModularCurve.DRModelPackageLevel.extendsToPlace_pts_add
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    ∀ (x y : JZero (N₀ * p)),
      ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ)) (pts x) →
      ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ)) (pts y) →
        ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ)) (pts (x + y)) := by sorry
