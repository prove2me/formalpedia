-- Prove2me | Theorems.Thm_ModularCurve_pts_lift_comp_theta_fst_eq_pts_of_dRModelPackage_of_igusaModel
-- name    : ModularCurve.pts_lift_comp_theta_fst_eq_pts_of_dRModelPackage_of_igusaModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/b921f139-aeb2-5255-9ddf-0b691a3f3674
-- title:
--   Igusa and Deligne–Rapoport point dictionaries agree through θ_ℚ
-- statement:
--   Fix a prime $p$ and a prime $\ell$. Write $\mathfrak{X} : \mathrm{DRModelPackage}\ p$ for the integral two-chart model data of $X_0(p)$: the scheme $\mathrm{DRModel}\ p = \mathrm{TwoChartIntegralModel}\ \mathbb{Z}\ F\ j$ built from the function field $F = \mathrm{modularFunctionFieldFull}\ p$ (the subfield of $\mathrm{LaurentSeries}\ \mathbb{Q}$ generated over $\mathbb{Q}$ by the divisor expansions of level $p$) and the Igusa parameter $j$, with structure morphism $\mathrm{DRModel.toBase}\ p$ to $\operatorname{Spec}\mathbb{Z}$, together with a curve model $\mathfrak{X}.M_0$ of $F$ over $\mathbb{Q}$ and an isomorphism $\mathfrak{X}.e_0$ onto the $\mathbb{Q}$-fibre, a curve model $\mathfrak{X}.M_\eta$ of $\bar F = \mathrm{modularFunctionFieldBar}\ p$ over $\overline{\mathbb{Q}}$ and an isomorphism $\mathfrak{X}.e_\eta$ onto the $\overline{\mathbb{Q}}$-fibre, and sections $\mathfrak{X}.\varepsilon_{\inf}$, $\mathfrak{X}.\varepsilon_{\mathrm{zero}}$ of $\mathrm{DRModel.toBase}\ p$. Here $\mathrm{DRModel.toBase}\ p$ is assumed proper. Recall $\mathrm{JZero}\ p = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \bar F)$, the group of degree-zero divisor classes on places of $\bar F$ over $\overline{\mathbb{Q}}$, and that for a curve model $M$ over an algebraically closed field, $M.\mathrm{pointEquivPlace}$ is the bijection between sections of $M.\mathrm{toBase}$ and places.
--
--   Deligne–Rapoport side. A relative $\mathrm{Pic}^0$ designation $D$ over $\mathbb{Z}$ for $\mathrm{DRModel.toBase}\ p$ (a scheme $D.P$ over $\operatorname{Spec}\mathbb{Z}$ with a zero section) is given, together with: `hD`, asserting that $D$ represents, via a Poincaré rigidified line bundle and a universal property, the subfunctor of rigidified line bundles on the relative curve rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ that are fibrewise algebraically equivalent to zero (the cut `algEquivZeroCut`); and `h'`, the corresponding representability statement for the base change of the curve to $\mathbb{Q}$, the base-changed section, and the designation $D.\mathrm{baseChange}\ \mathbb{Q} = D.P \times_{\operatorname{Spec}\mathbb{Z}} \operatorname{Spec}\mathbb{Q}$.
--
--   Further Deligne–Rapoport data: a morphism $aj_{\mathbb{Q}}$ from the $\mathbb{Q}$-fibre of the curve to $(D_{\mathbb{Q}}).\mathrm{toBase}$ over $\operatorname{Spec}\mathbb{Q}$; a morphism $aj : \mathfrak{X}.M_\eta.C \to D.P$; a $\overline{\mathbb{Q}}$-point $\bar\varepsilon$ of $\mathfrak{X}.M_\eta.C$ (a section of $\mathfrak{X}.M_\eta.\mathrm{toBase}$); and a bijection $\mathrm{pts}$ from $\mathrm{JZero}\ p$ to the $\overline{\mathbb{Q}}$-points of $D.\mathrm{toBase}$ over $\operatorname{Spec}\mathbb{Z}$. These are subject to the following hypotheses. `pts_add`: $\mathrm{pts}$ is additive for the relative group law on $D.\mathrm{toBase}$ supplied by `hD` for the group cut `algEquivZeroGroupCut`. `hP`: the Poincaré bundle of `h'` is isomorphic to the base change to $\mathbb{Q}$ of the pullback of the Poincaré bundle of `hD` along the first projection of $D.P \times_{\operatorname{Spec}\mathbb{Z}} \operatorname{Spec}\mathbb{Q}$. `hajε`: the base-changed section $\mathfrak{X}.\varepsilon_{\inf}$ followed by $aj_{\mathbb{Q}}$ is the zero section of $D.\mathrm{baseChange}\ \mathbb{Q}$. `haj` (Abel–Jacobi normalisation over $\mathbb{Q}$): for every field $K$, every $t : \operatorname{Spec}K \to \operatorname{Spec}\mathbb{Q}$ and every $K$-point $x$ of the $\mathbb{Q}$-fibre over $t$, the pullback of the Poincaré bundle of `h'` along $x$ followed by $aj_{\mathbb{Q}}$ is isomorphic to the tensor product of the line bundle (inverse ideal module) of the relative effective Cartier divisor cut out by $x$ with the ideal module of the divisor cut out by $t$ followed by the base-changed section. `hk₀`: there is a morphism $k_0$ from the $\overline{\mathbb{Q}}$-fibre pullback to the $\mathbb{Q}$-fibre pullback of $\mathrm{DRModel.toBase}\ p$ compatible with the first projections, compatible with the second projections up to $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Q}$, and such that $aj$ is $\mathfrak{X}.e_\eta$ followed by $k_0$, by $aj_{\mathbb{Q}}$ and by the first projection of $D.P \times_{\operatorname{Spec}\mathbb{Z}} \operatorname{Spec}\mathbb{Q}$. `haj_over`: $aj$ followed by $D.\mathrm{toBase}$ equals $\mathfrak{X}.M_\eta.\mathrm{toBase}$ followed by $\operatorname{Spec}$ of $\mathbb{Z} \to \overline{\mathbb{Q}}$. `hεbar`: $\bar\varepsilon$ followed by $\mathfrak{X}.e_\eta$ and the first projection equals $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Z}$ followed by $\mathfrak{X}.\varepsilon_{\inf}$. `hεbar_aj`: $\bar\varepsilon$ followed by $aj$ equals $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Z}$ followed by the zero section of $D$. `hpts_aj`: for every $\overline{\mathbb{Q}}$-point $x$ of $\mathfrak{X}.M_\eta.C$ there is a degree-zero divisor $Dv$ on $\bar F$ equal to $[\,\mathfrak{X}.M_\eta.\mathrm{pointEquivPlace}(x)\,] - [\,\mathfrak{X}.M_\eta.\mathrm{pointEquivPlace}(\bar\varepsilon)\,]$ whose class satisfies $\mathrm{pts}(\mathrm{Pic}^0.\mathrm{mk}\ Dv) = x$ followed by $aj$.
--
--   Igusa side. Let $R_\ell = \mathrm{GaloisRep.ratLocalizedAt}\ \ell$, the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $\ell$, and let $c : X \to \operatorname{Spec}R_\ell$ be proper, smooth of relative dimension $1$ and geometrically integral, with a section $\varepsilon$. A relative $\mathrm{Pic}^0$ designation $DP$ over $R_\ell$ is given with `hDP` asserting that it represents the fibrewise-algebraically-trivial rigidified line bundles for $c$ and $\varepsilon$. Further: a curve model $M_{0P}$ of $F$ over $\mathbb{Q}$ with an isomorphism $e_{0P}$ onto the $\mathbb{Q}$-fibre of $c$ satisfying `he₀P`; a curve model $M_{\eta P}$ of $\bar F$ over $\overline{\mathbb{Q}}$ with an isomorphism $e_{\eta P}$ onto the $\overline{\mathbb{Q}}$-fibre satisfying `heηP`; the hypothesis `hcompatP`, which says that for a $\overline{\mathbb{Q}}$-point $x$ of $M_{\eta P}.C$, a $\overline{\mathbb{Q}}$-point $y$ of the $\mathbb{Q}$-fibre of $c$ and a closed point $x_0$ of $M_{0P}.C$, if $y$ and $x$ have the same image in $X$ and $y$ followed by $e_{0P}^{-1}$ sends the closed point to $x_0$, then the valuation subring of the place $M_{\eta P}.\mathrm{pointEquivPlace}(x)$, pulled back along the composite of the right inclusion $F \to \overline{\mathbb{Q}} \otimes_{\mathbb{Q}} F$ with $\mathrm{baseChangeEquiv}$, is the valuation subring of $M_{0P}.\mathrm{placeOfPoint}(x_0)$.
--
--   Abel–Jacobi and dictionary data on the Igusa side: a morphism $aj_P$ from $X$ to $DP.\mathrm{toBase}$ over $\operatorname{Spec}R_\ell$ with `hajPε` saying that $\varepsilon$ followed by $aj_P$ is the zero section of $DP$, and `hajP` the Abel–Jacobi normalisation over $R_\ell$ in the same shape as `haj`; a bijection $\mathrm{pts}_P$ from $\mathrm{JZero}\ p$ to the $\overline{\mathbb{Q}}$-points of $DP.\mathrm{toBase}$ over $\operatorname{Spec}R_\ell$, with `ptsP_add` its additivity for the relative group law attached to `hDP`, and `ptsP_aj`: for all $\overline{\mathbb{Q}}$-points $x, s$ of $M_{\eta P}.C$ such that $s$ corresponds to $\varepsilon$ (that is, $s$ followed by $e_{\eta P}$ and the first projection equals $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}R_\ell$ followed by $\varepsilon$), there is a degree-zero divisor $Dv$ on $\bar F$ equal to $[M_{\eta P}.\mathrm{pointEquivPlace}(x)] - [M_{\eta P}.\mathrm{pointEquivPlace}(s)]$ with $\mathrm{pts}_P(\mathrm{Pic}^0.\mathrm{mk}\ Dv)$ equal to $x$ followed by $e_{\eta P}$, the first projection and $aj_P$.
--
--   Comparison data. An isomorphism $e_{36} : M_{0P}.C \cong \mathfrak{X}.M_0.C$ over $\mathbb{Q}$ (`he36`), with `hplace36` asserting that for every closed point $x$ of $M_{0P}.C$ the place $\mathfrak{X}.M_0.\mathrm{placeOfPoint}$ of its image equals the transport of $M_{0P}.\mathrm{placeOfPoint}(x)$ along the identity $\mathbb{Q}$-algebra automorphism of $F$. An isomorphism $e_{\mathbb{Q}}$ between the $\mathbb{Q}$-fibre of $c$ and the $\mathbb{Q}$-fibre of $\mathrm{DRModel.toBase}\ p$, compatible with the projections to $\operatorname{Spec}\mathbb{Q}$ in both directions (`heQ`, `heQ'`) and with the two trivialisations of the $\mathbb{Q}$-fibre through $e_{36}$ (`heQ₀`: $e_{0P}$ followed by $e_{\mathbb{Q}}$ equals $e_{36}$ followed by $\mathfrak{X}.e_0$). The hypothesis `hQ`, representability over $\mathbb{Q}$ on the Igusa side for $DP.\mathrm{baseChange}\ \mathbb{Q}$, and `hPQ`, the corresponding Poincaré base-change isomorphism for `hDP`. Finally a morphism $\theta_{\mathbb{Q}}$ from $(DP.\mathrm{baseChange}\ \mathbb{Q}).\mathrm{toBase}$ to $(D.\mathrm{baseChange}\ \mathbb{Q}).\mathrm{toBase}$ over $\operatorname{Spec}\mathbb{Q}$, subject to `hθQ`: for every $T \to \operatorname{Spec}\mathbb{Q}$, every rigidified line bundle $M$ on the Igusa $\mathbb{Q}$-curve and every rigidified line bundle $N$ on the Deligne–Rapoport $\mathbb{Q}$-curve, both fibrewise algebraically trivial, and every invertible module $Q$ on $T$, an isomorphism of $N.L$ with the tensor product of the pullback of $M.L$ along the curve change induced by $e_{\mathbb{Q}}^{-1}$ and the pullback of $Q$ to the relative curve forces the classifying map of $M$ for `hQ`, post-composed with $\theta_{\mathbb{Q}}$, to equal the classifying map of $N$ for `h'`.
--
--   Conclusion: for every $x \in \mathrm{JZero}\ p$, the $\overline{\mathbb{Q}}$-point of $DP.P \times_{\operatorname{Spec}R_\ell} \operatorname{Spec}\mathbb{Q}$ determined by $(\mathrm{pts}_P\ x)$ and by $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Q}$ (the lift exists because $(\mathrm{pts}_P\ x)$ lies over $\operatorname{Spec}R_\ell$ compatibly with $R_\ell \to \mathbb{Q} \to \overline{\mathbb{Q}}$), followed by $\theta_{\mathbb{Q}}$ and then by the first projection $D.P \times_{\operatorname{Spec}\mathbb{Z}} \operatorname{Spec}\mathbb{Q} \to D.P$, equals $(\mathrm{pts}\ x)$ as a morphism $\operatorname{Spec}\overline{\mathbb{Q}} \to D.P$.
--
--   This is the compatibility step identifying the two dictionaries for $\overline{\mathbf{Q}}$-points of $J_0(p)$ — one attached to the integral two-chart (Deligne–Rapoport style) model of $X_0(p)$ over $\mathbf{Z}$, the other to a smooth proper model over $\mathbf{Z}_{(\ell)}$ of Igusa type — through the comparison morphism $\theta_{\mathbf{Q}}$ of the two relative $\mathrm{Pic}^0$ representing objects over $\mathbf{Q}$. It is used by [`ModularCurve.exists_pointsDict_pullback_snd_ratLocalizedAt_of_dRModelPackage_of_representsRelSubPic`](thm.html#ModularCurve.exists_pointsDict_pullback_snd_ratLocalizedAt_of_dRModelPackage_of_representsRelSubPic), which transports the points dictionary to the $\mathbf{Z}_{(\ell)}$-model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pts_lift_comp_theta_fst_eq_pts_of_dRModelPackage_of_igusaModel.lean

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
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing

set_option maxHeartbeats 800000 in

theorem ModularCurve.pts_lift_comp_theta_fst_eq_pts_of_dRModelPackage_of_igusaModel
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) [IsProper (DRModel.toBase p)]
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    (h' : RepresentsRelSubPic (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
      (algEquivZeroCut (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange ℤ (DRModel.toBase p) ℚ) (D.baseChange ℚ).toBase)
    (aj : 𝔛.Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase)
    (pts_add : ∀ x y : JZero p, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _ (pts x) (pts y))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR (DRModel.toBase p) 𝔛.εinf ℚ
      (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ℤ ℚ), pullback.condition⟩)).L))
    (hajε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange ℤ (DRModel.toBase p) ℚ)),
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (hk₀ : ∃ k₀ : pullback (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ⟶ pullback (DRModel.toBase p) (specMap ℤ ℚ),
        k₀ ≫ pullback.fst (DRModel.toBase p) (specMap ℤ ℚ) = pullback.fst (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ∧
        k₀ ≫ pullback.snd (DRModel.toBase p) (specMap ℤ ℚ) =
          pullback.snd (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧
        aj = 𝔛.eη ≫ k₀ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap ℤ ℚ))
    (haj_over : aj ≫ D.toBase = 𝔛.Mη.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (hεbar : εbar.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ =
        Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ aj = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ D.zeroSection)
    (hpts_aj : ∀ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _},
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)) =
            Finsupp.single (𝔛.Mη.pointEquivPlace x) 1 - Finsupp.single (𝔛.Mη.pointEquivPlace εbar) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ aj)
    (ℓ : ℕ) [Fact ℓ.Prime]

    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (DP : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (hDP : RepresentsRelSubPic c ε (algEquivZeroCut c ε) DP)
    (M₀P : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀P : M₀P.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) [IsIso e₀P]
    (he₀P : e₀P ≫ pullback.snd c _ = M₀P.toBase)
    (MηP : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eηP : MηP.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eηP]
    (heηP : eηP ≫ pullback.snd c _ = MηP.toBase)
    (hcompatP : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ MηP.C // q ≫ MηP.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))))
        (x₀ : closedPoints M₀P.C),
      y ≫ pullback.fst c _ = x.1 ≫ eηP ≫ pullback.fst c _ →
      (y ≫ inv e₀P).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((MηP.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull p))).toRingHom) =
        (M₀P.placeOfPoint x₀).toValuationSubring.toSubring))
    (ajP : SchemeHomOver c DP.toBase) (hajPε : ε.1 ≫ ajP.1 = DP.zeroSection)
    (hajP : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x : SchemeHomOver t c),
        Nonempty ((hDP.poincare.pullbackAlong
            ⟨x.1 ≫ ajP.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajP.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (ptsP : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) DP.toBase)
    (ptsP_add : ∀ x y : JZero p, ptsP (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hDP).mul _ (ptsP x) (ptsP y))
    (ptsP_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ MηP.C // q ≫ MηP.toBase = 𝟙 _}),
        s.1 ≫ eηP ≫ pullback.fst c _ =
          Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
          (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
            Finsupp.single (MηP.pointEquivPlace x) 1 - Finsupp.single (MηP.pointEquivPlace s) 1 ∧
          (ptsP (Pic0.mk Dv)).1 = x.1 ≫ eηP ≫ pullback.fst c _ ≫ ajP.1)

    (e36 : M₀P.C ≅ 𝔛.M₀.C) (he36 : e36.hom ≫ 𝔛.M₀.toBase = M₀P.toBase)
    (hplace36 : ∀ x : closedPoints M₀P.C,
        𝔛.M₀.placeOfPoint ⟨e36.hom.base x.1, by
            show IsClosed ({e36.hom.base x.1} : Set 𝔛.M₀.C)
            rw [← Set.image_singleton]
            exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e36)).isClosedMap _ x.2⟩
          = Place.congrRingEquiv (AlgEquiv.refl : ↥(modularFunctionFieldFull p) ≃ₐ[ℚ] ↥(modularFunctionFieldFull p)).toRingEquiv
              (fun a => (AlgEquiv.refl : ↥(modularFunctionFieldFull p) ≃ₐ[ℚ] ↥(modularFunctionFieldFull p)).commutes a)
              (M₀P.placeOfPoint x))
    (eQ : pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) ≅ pullback (DRModel.toBase p) (specMap ℤ ℚ))
    (heQ : eQ.hom ≫ pullback.snd _ _ = pullback.snd _ _) (heQ' : eQ.inv ≫ pullback.snd _ _ = pullback.snd _ _)
    (heQ₀ : e₀P ≫ eQ.hom = e36.hom ≫ 𝔛.e₀)
    (hQ : RepresentsRelSubPic (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) (DP.baseChange ℚ))
    (hPQ : Nonempty (hQ.poincare.L ≅ (BaseChange.ofR c ε ℚ
      (hDP.poincare.pullbackAlong ⟨pullback.fst DP.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ), pullback.condition⟩)).L))
    (θQ : SchemeHomOver (DP.baseChange ℚ).toBase (D.baseChange ℚ).toBase)
    (hθQ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf) t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ)
            (c' := baseChange ℤ (DRModel.toBase p) ℚ) eQ.inv heQ' t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd (baseChange ℤ (DRModel.toBase p) ℚ) t)).obj Q) →
        postComp θQ (hQ.classify t M hM) = h'.classify t N hN) :
    ∀ x : JZero p,
      pullback.lift (ptsP x).1 (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
          (by rw [(ptsP x).2, specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]) ≫
        θQ.1 ≫ pullback.fst D.toBase (specMap ℤ ℚ) = (pts x).1 := by sorry
