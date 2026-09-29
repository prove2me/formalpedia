-- Prove2me | Theorems.Thm_ModularCurve_coe_ffEquiv_symm_stalkMap_eq_coeffEmb_ffEquiv_symm_of_galoisCompat_of_placeCompat
-- name    : ModularCurve.coe_ffEquiv_symm_stalkMap_eq_coeffEmb_ffEquiv_symm_of_galoisCompat_of_placeCompat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/1a5d73c4-d850-5ad7-b234-525df31c1da7
-- title:
--   Geometric function field identification is base change of the rational one
-- statement:
--   Fix $N\ge 1$ and a prime $p$, and let $c\colon X\to\operatorname{Spec}R$ be a scheme over $R=\mathbb{Q}_{(p)}$, the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $p$. Let $M_0$ be a curve model of $F_N=\mathbb{Q}(\text{divisorExpansions }N)\subset\mathbb{Q}((q))$ over $\mathbb{Q}$, that is: an integral scheme $M_0.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\mathbb{Q}$, together with a ring isomorphism $M_0.\mathrm{ffEquiv}\colon F_N\xrightarrow{\sim}\mathcal{K}(M_0.C)$ compatible with the structure map on $\mathbb{Q}$, a bijection $M_0.\mathrm{placeOfPoint}$ from closed points to places of $F_N/\mathbb{Q}$ matching each stalk with the corresponding valuation subring, and the property that every finite set of points lies in an affine open; let $e_0$ be an isomorphism $M_0.C\cong X\times_R\mathbb{Q}$ with $e_0$ followed by the second projection equal to $M_0.\mathrm{toBase}$. Let $M_\eta$ be a curve model, in the same sense, of $\bar F_N=\mathrm{laurentBaseChange}(\bar{\mathbb{Q}},F_N)\subset\bar{\mathbb{Q}}((q))$ over $\bar{\mathbb{Q}}=\mathrm{AlgebraicClosure}\ \mathbb{Q}$, with an isomorphism $e_\eta\colon M_\eta.C\cong X\times_R\bar{\mathbb{Q}}$ satisfying the analogous compatibility with $M_\eta.\mathrm{toBase}$. Two hypotheses are imposed. Galois compatibility: for every $g\in\operatorname{Aut}_{\mathbb{Q}}(\bar{\mathbb{Q}})$ and any two sections $x,x'$ of $M_\eta.\mathrm{toBase}$, if the $X$-point $x'\rightsquigarrow M_\eta.C\to X$ equals $\operatorname{Spec}(g)$ followed by the $X$-point of $x$, then the place attached to $x'$ by $M_\eta.\mathrm{pointEquivPlace}$ is the image of the place attached to $x$ under the action $\mathrm{arithmeticGalois}(F_N)(g)$. Place compatibility: for every section $x$ of $M_\eta.\mathrm{toBase}$, every $\bar{\mathbb{Q}}$-point $y$ of $X\times_R\mathbb{Q}$ and every closed point $x_0$ of $M_0.C$, if $y$ and $x$ give the same point of $X$ and if $y$ followed by $e_0^{-1}$ sends the closed point of $\bar{\mathbb{Q}}$ to $x_0$, then the valuation subring of $M_\eta.\mathrm{pointEquivPlace}\,x$, pulled back along $F_N\to\bar{\mathbb{Q}}\otimes_{\mathbb{Q}}F_N\xrightarrow{\ \mathrm{baseChangeEquiv}\ }\bar F_N$, is the valuation subring of $M_0.\mathrm{placeOfPoint}\,x_0$. Finally let $\theta\colon M_\eta.C\to M_0.C$ be a morphism over $X$, in the sense that $\theta$ followed by $e_0$ and the first projection equals $e_\eta$ followed by the first projection. The conclusion is that for every point $P$ of $M_\eta.C$ and every germ $s$ in the stalk of $M_0.C$ at $\theta(P)$, the element $M_\eta.\mathrm{ffEquiv}^{-1}$ of the image in $\mathcal{K}(M_\eta.C)$ of $(\mathrm{stalkMap}\ \theta\ P)(s)$, viewed in $\bar{\mathbb{Q}}((q))$, equals $\mathrm{coeffEmb}$, the coefficientwise map induced by $\mathbb{Q}\hookrightarrow\bar{\mathbb{Q}}$, applied to $M_0.\mathrm{ffEquiv}^{-1}$ of the image of $s$ in $\mathcal{K}(M_0.C)$, viewed in $\mathbb{Q}((q))$.
--
--   This is the statement that the identification of the function field of the geometric fibre $X_{\bar{\mathbb{Q}}}$ with $\bar F_N\subset\bar{\mathbb{Q}}((q))$ carried by $M_\eta$ agrees, on germs pulled back from the rational model, with the coefficientwise base change of the identification carried by $M_0$; the Galois- and place-compatibility hypotheses are what pin the two identifications together. It is used in the computations of the order of vanishing of the modular functions $j(q^d)$ at points of the geometric fibre, where an explicit Laurent expansion known over $\mathbb{Q}$ must be read off over $\bar{\mathbb{Q}}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_ffEquiv_symm_stalkMap_eq_coeffEmb_ffEquiv_symm_of_galoisCompat_of_placeCompat.lean

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm

theorem ModularCurve.coe_ffEquiv_symm_stalkMap_eq_coeffEmb_ffEquiv_symm_of_galoisCompat_of_placeCompat
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)

    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g • Mη.pointEquivPlace x)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))

    (θ : Mη.C ⟶ M₀.C) (hθ : θ ≫ e₀ ≫ pullback.fst c _ = eη ≫ pullback.fst c _)
    (P : Mη.C) (s : M₀.C.presheaf.stalk (θ.base P)) :
    ((Mη.ffEquiv.symm (algebraMap (Mη.C.presheaf.stalk P) Mη.C.functionField
        ((Scheme.Hom.stalkMap θ P).hom s)) : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ)
        ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk (θ.base P)) M₀.C.functionField s) :
          ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) := by sorry
