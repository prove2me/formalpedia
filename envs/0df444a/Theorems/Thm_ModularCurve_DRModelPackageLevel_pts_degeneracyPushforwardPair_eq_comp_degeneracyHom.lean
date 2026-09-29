-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_pts_degeneracyPushforwardPair_eq_comp_degeneracyHom
-- name    : ModularCurve.DRModelPackageLevel.pts_degeneracyPushforwardPair_eq_comp_degeneracyHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/713e65a2-ac41-5142-8237-a87b4f53d9f0
-- title:
--   Norm morphisms realise the degeneracy pushforwards on ℚ̄-points
-- statement:
--   Fix a positive integer $N_0$ and a prime $p$ with $p \nmid N_0$, a Deligne–Rapoport package $\mathfrak{P}$ of level $N_0p$ at $p$, and assume the Igusa-type structure morphism `toBase N₀ p` over $R p$ is proper. Let $D$ be a relative $\mathrm{Pic}^0$ designation over $R p$ for that curve, with $hD$ asserting that $D$ represents the functor of line bundles rigidified along the section $\mathfrak{P}.\varepsilon_{\inf}$ whose geometric fibres are algebraically equivalent to zero, and $hDQ$ the same for the base change to $\mathbb{Q}$ and $D.\mathrm{baseChange}\ \mathbb{Q}$; $hPQ$ identifies the two Poincaré bundles. Further data: an Abel–Jacobi morphism $aj_{\mathbb{Q}}$ over $\mathbb{Q}$ carrying the $\infty$-section to the zero section ($haj_{\mathbb{Q}}\varepsilon$) and computing, on points over any field, the class of the point minus $\infty$ ($haj_{\mathbb{Q}}$); a comparison morphism $k_{\mathbb{Q}}$ between the fibre over $\mathrm{Spec}\,\bar{\mathbb{Q}}$ and the fibre over $\mathrm{Spec}\,\mathbb{Q}$ with its two compatibilities; the induced $\bar{\mathbb{Q}}$-level morphism $\overline{aj}$ from the curve model $\mathfrak{P}.\mathrm{Meta}$ to $D.P$, equal to $\mathfrak{P}.\mathrm{eeta}$ followed by $k_{\mathbb{Q}}$, $aj_{\mathbb{Q}}$ and the first projection, lying over `genPt p`; a $\bar{\mathbb{Q}}$-point $\bar\varepsilon$ of $\mathfrak{P}.\mathrm{Meta}$ sitting over $\varepsilon_{\inf}$ and killed by $\overline{aj}$; and a bijection $\mathrm{pts}$ from $\mathrm{Pic}^0$ of the geometric modular function field of level $N_0p$ to the $\bar{\mathbb{Q}}$-points of $D.\mathrm{toBase}$ which is additive for the relative group law coming from $hD$, Galois-equivariant, and normalised by $\overline{aj}$ in the sense that for $\bar{\mathbb{Q}}$-points $x,s$ of $\mathfrak{P}.\mathrm{Meta}$ with $s$ over $\varepsilon_{\inf}$ there is a degree-zero divisor equal to $[x]-[s]$ whose class is sent by $\mathrm{pts}$ to $x$ followed by $\overline{aj}$. Let also $A$ be a valuation subring of $\bar{\mathbb{Q}}$, $M$ a level-$N_0$ model over $A$ with $M.\mathrm{toLevelData}$ satisfying `IsJacobian`. Assume $\mathfrak{P}.\pi$ is finite, flat and locally of finite presentation with all fibre ranks $p+1$, and let $\delta_0,\delta_1 : D.P \to M.D_0.P$ be morphisms over $\mathrm{Spec}\,R p$ such that, for every $T$-point $a$ of $D.\mathrm{toBase}$, the pullback of $M$'s Poincaré bundle along $a$ followed by $\delta_i$ is isomorphic to the rank-$(p+1)$ norm module along the curve change of $\mathfrak{P}.\pi$ (for $i=0$) respectively $\mathfrak{P}.\pi_w$ (for $i=1$) of the pullback of $hD$'s Poincaré bundle along $a$, rigidified along $M.\varepsilon_0$, and such that each $\delta_i$ is a homomorphism for the two relative group laws. The conclusion: for $i \in \{0,1\}$ and every class $x$ in $\mathrm{Pic}^0$ of level $N_0p$, the point $M.\mathrm{pts}$ of the image of $x$ under the $i$-th degeneracy pushforward `degeneracyPushforwardPair N₀ p i` equals $\mathrm{pts}(x)$ followed by $\delta_i$.
--
--   This is the Albanese (pushforward) functoriality of the two degeneracy maps $\alpha_*,\beta_* : J_0(N_0p) \to J_0(N_0)$, expressed as the statement that the morphisms classifying the norm of the Poincaré bundle along $\pi$ and along $w\pi$ induce, on $\bar{\mathbb{Q}}$-points, exactly the pushforward of degree-zero divisor classes along the two inclusions of modular function fields. It is the generic-points clause used in building the Hecke action on the level-$N_0p$ Néron object and in the existence theorem for that object together with its comparison with the level-$N_0$ model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_pts_degeneracyPushforwardPair_eq_comp_degeneracyHom.lean

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

theorem ModularCurve.DRModelPackageLevel.pts_degeneracyPushforwardPair_eq_comp_degeneracyHom
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

    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A) (hM : M.toLevelData.IsJacobian)

    [IsFinite 𝔓.π.1] [Flat 𝔓.π.1] [LocallyOfFinitePresentation 𝔓.π.1] (hrk : ∀ x, 𝔓.π.1.finrank x = p + 1)
    (δ : Fin 2 → SchemeHomOver D.toBase M.D₀.toBase)
    (hδ₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((M.rep.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 0))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t M.ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.π.1 𝔓.π.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδ₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((M.rep.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 1))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t M.ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.πw.1 𝔓.πw.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδhom : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) (δ i) =
        M.law.mul t (NeronModelInfra.schemeHomOverComp x (δ i)) (NeronModelInfra.schemeHomOverComp y (δ i))) :
    ∀ (i : Fin 2) (x : JZero (N₀ * p)),
      (M.pts (degeneracyPushforwardPair N₀ p i x)).1 = (pts x).1 ≫ (δ i).1 := by sorry
