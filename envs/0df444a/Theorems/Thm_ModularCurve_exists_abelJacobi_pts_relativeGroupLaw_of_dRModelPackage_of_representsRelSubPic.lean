-- Prove2me | Theorems.Thm_ModularCurve_exists_abelJacobi_pts_relativeGroupLaw_of_dRModelPackage_of_representsRelSubPic
-- name    : ModularCurve.exists_abelJacobi_pts_relativeGroupLaw_of_dRModelPackage_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/e168b82d-9248-58a9-9f14-2364ecb703ba
-- title:
--   Relative Pic⁰ of the Deligne–Rapoport model: group law and points
-- statement:
--   Fix a prime $p$, a Deligne–Rapoport model datum $\mathfrak X$ of type `DRModelPackage p` for the two-chart integral model `DRModel p` of the full modular function field of level $p$ over $\mathbb Z$, together with a datum $I$ of type `𝔛.LegTwoInput`, properness of `DRModel.toBase p`, and the assumption that $\overline{\mathbb Q} \subset$ `modularFunctionFieldBar p` is a curve over $\overline{\mathbb Q}$ in the sense of `IsCurveOver` (principal divisors exist and have degree zero, all residue fields of places are finite over $\overline{\mathbb Q}$, and the module of Kähler differentials is free of rank one). Let $D$ be a pointed $\mathbb Z$-scheme datum `RelativePic0Designation ℤ (DRModel.toBase p)`, i.e. a scheme $D.P$ with structure map $D.\mathrm{toBase}$ to $\operatorname{Spec}\mathbb Z$ and a zero section, and assume $hD$: $D$ represents the rigidified relative Picard functor of $(\mathfrak X, \varepsilon_\infty)$ cut out by `algEquivZeroCut`, the condition that a rigidified invertible module be fibrewise algebraically equivalent to zero; assume also that $D.\mathrm{toBase}$ is smooth and geometrically connected. Then there exist: a representability datum $h'$ for the base change of $D$ to $\mathbb Q$ with respect to the base-changed section; a morphism $aj_{\mathbb Q}$ over $\mathfrak X_{\mathbb Q}$ into $(D_{\mathbb Q}).\mathrm{toBase}$; a morphism $aj : \mathfrak X.M_\eta.C \to D.P$; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak X.M_\eta.C$; and a bijection $\mathrm{pts}$ from `JZero p` $=\operatorname{Pic}^0(\overline{\mathbb Q},$ `modularFunctionFieldBar p`$)$ onto the $\overline{\mathbb Q}$-points of $D.\mathrm{toBase}$, such that: the relative group law on $D.\mathrm{toBase}$ furnished by $hD$ (for the group-valued cut `algEquivZeroGroupCut`) is commutative; $D.\mathrm{toBase}$ is locally of finite type; every set-theoretic fibre of $D.\mathrm{toBase}$ over a point of $\operatorname{Spec}\mathbb Z$ is preconnected; $\mathrm{pts}$ is additive for that group law; $\mathrm{pts}$ is equivariant for $\sigma \in \operatorname{Aut}(\overline{\mathbb Q}/\mathbb Q)$, the action on `JZero p` corresponding to precomposition with $\operatorname{Spec}\sigma$; the base change of $D.\mathrm{toBase}$ along $\mathbb Z \to \mathbb Z[1/p]$ is proper; the Poincaré bundle of $h'$ is isomorphic to the transport to $\mathbb Q$ (`BaseChange.ofR`) of the pullback of the Poincaré bundle of $hD$ along the first projection; $aj_{\mathbb Q}$ carries the base-changed section $\varepsilon_\infty$ to the zero section of $D_{\mathbb Q}$; for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb Q$ and every $t$-point $x$ of $\mathfrak X_{\mathbb Q}$, the pullback of the Poincaré bundle of $h'$ along $x$ followed by $aj_{\mathbb Q}$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of $t$ followed by the base-changed $\varepsilon_\infty$; there is a morphism $k_0$ from the $\overline{\mathbb Q}$-base change of `DRModel p` to its $\mathbb Q$-base change compatible with the first projection and, after $\operatorname{Spec}\overline{\mathbb Q} \to \operatorname{Spec}\mathbb Q$, with the second, for which $aj$ equals $\mathfrak X.e_\eta$ followed by $k_0$, $aj_{\mathbb Q}$ and the first projection; $aj$ followed by $D.\mathrm{toBase}$ equals $\mathfrak X.M_\eta.\mathrm{toBase}$ followed by $\operatorname{Spec}\overline{\mathbb Q} \to \operatorname{Spec}\mathbb Z$; $\bar\varepsilon$ followed by $e_\eta$ and the first projection is the $\overline{\mathbb Q}$-point induced by $\varepsilon_\infty$, and $\bar\varepsilon$ followed by $aj$ is the $\overline{\mathbb Q}$-point induced by the zero section; and, for every $\overline{\mathbb Q}$-point $x$ of $\mathfrak X.M_\eta.C$, there is a degree-zero divisor $D_v$ on `modularFunctionFieldBar p` equal to the difference of the indicator divisors of the places $\mathfrak X.M_\eta.\mathrm{pointEquivPlace}\,x$ and $\mathfrak X.M_\eta.\mathrm{pointEquivPlace}\,\bar\varepsilon$, whose class satisfies $\mathrm{pts}([D_v]) = x$ followed by $aj$.
--
--   This is the arithmetic package for the Jacobian $J_0(p)$ realised as the relative $\operatorname{Pic}^0$ of the Deligne–Rapoport model of $X_0(p)$ over $\mathbb Z$: commutativity of the group law, finiteness and connectedness properties of the structure morphism, properness away from $p$, compatibility of the Picard functor with base change to $\mathbb Q$, the Abel–Jacobi morphism normalised at the cusp $\infty$ and classifying $\mathcal O(\Gamma_x) \otimes \mathcal O(-\varepsilon)$, and a Galois-equivariant additive identification of the degree-zero divisor class group of the modular function field over $\overline{\mathbb Q}$ with the $\overline{\mathbb Q}$-points of $D$. It supplies the data consumed by [`ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin`](thm.html#ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin), where the good-reduction identity component of $J_0(p)$ away from $p$ is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_abelJacobi_pts_relativeGroupLaw_of_dRModelPackage_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.exists_abelJacobi_pts_relativeGroupLaw_of_dRModelPackage_of_representsRelSubPic
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (I : 𝔛.LegTwoInput) [IsProper (DRModel.toBase p)]
    [IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)]
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    (hsm : Smooth D.toBase) (hconn : GeometricallyConnected D.toBase) :
    ∃ (h' : RepresentsRelSubPic (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
      (ajQ : SchemeHomOver (baseChange ℤ (DRModel.toBase p) ℚ) (D.baseChange ℚ).toBase)
      (aj : 𝔛.Mη.C ⟶ D.P)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
      (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase),

      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).IsCommutative ∧
      LocallyOfFiniteType D.toBase ∧
      (∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (D.toBase.base ⁻¹' {s})) ∧
      (∀ x y : JZero p, pts (x + y) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _
          (pts x) (pts y)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
        (pts (σ • x)).1 =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1) ∧
      IsProper (pullback.snd D.toBase
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))) ∧

      Nonempty (h'.poincare.L ≅ (BaseChange.ofR (DRModel.toBase p) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ℤ ℚ), pullback.condition⟩)).L) ∧

      (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection ∧
      (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange ℤ (DRModel.toBase p) ℚ)),
        Nonempty ((h'.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule)) ∧

      (∃ k₀ : pullback (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ⟶ pullback (DRModel.toBase p) (specMap ℤ ℚ),
        k₀ ≫ pullback.fst (DRModel.toBase p) (specMap ℤ ℚ) = pullback.fst (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ∧
        k₀ ≫ pullback.snd (DRModel.toBase p) (specMap ℤ ℚ) =
          pullback.snd (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧
        aj = 𝔛.eη ≫ k₀ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap ℤ ℚ)) ∧
      aj ≫ D.toBase = 𝔛.Mη.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ∧
      εbar.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ =
        Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ 𝔛.εinf.1 ∧
      εbar.1 ≫ aj = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ D.zeroSection ∧
      ∀ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _},
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)) =
            Finsupp.single (𝔛.Mη.pointEquivPlace x) 1 - Finsupp.single (𝔛.Mη.pointEquivPlace εbar) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ aj := by sorry
