-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_mul_degeneracyHom_ajbar_abelJacobi_eq
-- name    : ModularCurve.DRModelPackageLevel.mul_degeneracyHom_ajbar_abelJacobi_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/e36dbab8-3a9a-5361-a4bd-5d4f39dcd794
-- title:
--   Degeneracy norm morphism versus Abel–Jacobi on ℚ̄-points
-- statement:
--   Fix $N_0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak{P}$ be a `DRModelPackageLevel` for $N_0,p$, with the structure morphism `toBase N₀ p` of the level-$N_0p$ Igusa scheme proper over $\mathrm{Spec}$ of the coefficient ring `R p`. Let $D$ be a relative $\mathrm{Pic}^0$ designation (a scheme with a structure morphism to the base and a zero section) for `toBase N₀ p`, with `hD` asserting that $D$ represents rigidified line bundles satisfying the fibrewise algebraically-equivalent-to-zero condition `algEquivZeroCut` relative to the section $\mathfrak{P}.\varepsilon_{\inf}$, `hDQ` the analogous representability of the base change $D_{\mathbf{Q}}$ over $\mathbf{Q}$, and `hPQ` an isomorphism between the Poincaré bundle of `hDQ` and the base change to $\mathbf{Q}$ of the pullback along `pullback.fst` of the Poincaré bundle of `hD`. Let $aj_{\mathbf{Q}}$ be a section of the generic-fibre curve into $D_{\mathbf{Q}}$ carrying the base-changed $\varepsilon_{\inf}$ to the zero section, and such that for every field $K$, every $t : \mathrm{Spec}\,K \to \mathrm{Spec}\,\mathbf{Q}$ and every $K$-point $x$ of the curve over $\mathbf{Q}$, the pullback of the Poincaré bundle along $x$ followed by $aj_{\mathbf{Q}}$ is isomorphic to the line bundle (dual of the ideal module) of the graph divisor of $x$ tensored with the ideal module of the divisor cut out by $t$ followed by the base-changed $\varepsilon_{\inf}$. Let $k_{\mathbf{Q}}$ be the morphism from the fibre over $\overline{\mathbf{Q}}$ to the fibre over $\mathbf{Q}$ compatible with both projections (the second up to $\mathrm{Spec}$ of $\mathbf{Q} \to \overline{\mathbf{Q}}$), let $\overline{aj} : \mathfrak{P}.\mathrm{Meta}.C \to D.P$ be given by $\mathfrak{P}.eeta$ followed by $k_{\mathbf{Q}}$, $aj_{\mathbf{Q}}$ and `pullback.fst`, lying over $\mathfrak{P}.\mathrm{Meta}.\mathrm{toBase}$ followed by the geometric generic point `genPt p`, and let $\bar\varepsilon$ be a $\overline{\mathbf{Q}}$-point of $\mathfrak{P}.\mathrm{Meta}.C$ whose image in the curve is `genPt p` followed by $\varepsilon_{\inf}$ and which $\overline{aj}$ sends to the zero section. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ and $M$ a `LevelModel N₀ p A` whose associated level data satisfies `IsJacobian` (abelian-scheme properties, commutativity of the group law, additivity and Galois equivariance of the point parametrisations, compatibility of reduction, and existence of Hecke endomorphisms; summarised here). Assume $\mathfrak{P}.\pi$ is finite, flat and locally of finite presentation of constant rank $p+1$, and let $\delta : \mathrm{Fin}\,2 \to$ morphisms $D.P \to M.D_0.P$ over the base be such that $\delta\,0$ classifies norms: for every $T$-point $a$ of $D.\mathrm{toBase}$, the pullback of $M.\mathrm{rep}$'s Poincaré bundle along $a$ followed by $\delta\,0$ is isomorphic to the rigidification along `rigSection` of the degree-$(p+1)$ norm module, taken along the curve-change of $\mathfrak{P}.\pi$, of the pullback of `hD`'s Poincaré bundle along $a$. Finally let $y$ be a $\overline{\mathbf{Q}}$-point of $\mathfrak{P}.\mathrm{Meta}.C$ and $x, x_\infty$ be $\overline{\mathbf{Q}}$-points of $M.\mathrm{Meta}_0.C$ whose images in the level-$N_0$ curve are the images of $y$, respectively $\bar\varepsilon$, composed with $\mathfrak{P}.\pi$, and let $a,b,c$ be $\overline{\mathbf{Q}}$-points of $M.D_0.\mathrm{toBase}$ over `genPt p` given by $y$ followed by $\overline{aj}$ and then $\delta\,0$, by $x_\infty$ and $x$ followed by $M.eeta_0$, `pullback.fst` and $M.aj_0$ respectively. Then $a \cdot b = c$ for the group law `M.law` on $M.D_0.\mathrm{toBase}$ obtained from the representability of the algebraically-equivalent-to-zero subgroup condition.
--
--   This is the geometric-generic-point form of the identity $\delta_0(\overline{aj}(y)) \cdot aj_0(x_\infty) = aj_0(x)$, expressing that the norm along the degree-$(p+1)$ degeneracy morphism $\pi$ of $\mathcal{O}(y - \bar\varepsilon)$ is $\mathcal{O}(\pi y - \pi\bar\varepsilon)$, read through the two Abel–Jacobi normalisations. It is used to identify the degeneracy homomorphism $\delta\,0$ with the induced map on points of $J_0$, in [`ModularCurve.DRModelPackageLevel.pts_degeneracyPushforwardPair_eq_comp_degeneracyHom`](thm.html#ModularCurve.DRModelPackageLevel.pts_degeneracyPushforwardPair_eq_comp_degeneracyHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_mul_degeneracyHom_ajbar_abelJacobi_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel
  ModularCurve.JZeroNeronObjectAtP AlgebraicCurve

theorem ModularCurve.DRModelPackageLevel.mul_degeneracyHom_ajbar_abelJacobi_eq
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
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A) (hM : M.toLevelData.IsJacobian)

    [IsFinite 𝔓.π.1] [Flat 𝔓.π.1] [LocallyOfFinitePresentation 𝔓.π.1] (hrk : ∀ x, 𝔓.π.1.finrank x = p + 1)
    (δ : Fin 2 → SchemeHomOver D.toBase M.D₀.toBase)
    (hδ₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((M.rep.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 0))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t M.ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.π.1 𝔓.π.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (x xinf : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _})
    (hyx : x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.π.1)
    (hxinf : xinf.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.π.1)

    (a b c : SchemeHomOver (genPt p) M.D₀.toBase)
    (ha : a.1 = (y.1 ≫ ajbar) ≫ (δ 0).1)
    (hb : b.1 = xinf.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ M.aj₀.1)
    (hc : c.1 = x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ M.aj₀.1) :
    M.law.mul (genPt p) a b = c := by sorry
