-- Prove2me | Theorems.Thm_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_mul_stalkSpecializes_eq_jq_inv_cuspSection_of_ratCurveModel_compat_of_neZero
-- name    : ModularCurve.exists_isUnit_stalk_ffEquiv_symm_stalkMap_mul_stalkSpecializes_eq_jq_inv_cuspSection_of_ratCurveModel_compat_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/a39c214b-8795-5df0-bf1b-f8f2452f586f
-- title:
--   Cusp parameter has q-expansion 1/j up to a unit
-- statement:
--   Fix $N\ge 1$, a prime $p$ with $p\nmid N$, and write $R=\mathbb{Q}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $c\colon X\to\operatorname{Spec} R$ be proper and smooth of relative dimension $1$ with $X$ integral. The data are: a curve model $M_0$ over $\mathbb{Q}$ of the field $F_N=$ `modularFunctionFieldFull N` (the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the series $\mathrm{qExpand}\,d\,j$ for $0\ne d\mid N$) together with an isomorphism $e_0$ of $M_0.C$ onto $X\times_{\operatorname{Spec}R}\operatorname{Spec}\mathbb{Q}$ over the base; a section $\varepsilon_\infty$ of $c$; a closed point $x_0$ of $M_0.C$ whose associated place is `cuspInftyFull N`, the $q$-adic place attached to $j$; a $\mathbb{Q}$-point $y$ of the base change lying over the identity, inducing $\varepsilon_\infty$ on $X$ and carrying the closed point of $\mathbb{Q}$ to $x_0$ through $e_0^{-1}$; a curve model $M_\eta$ over $\overline{\mathbb{Q}}$ of `modularFunctionFieldBar N` with an isomorphism $e_\eta$ onto the base change to $\overline{\mathbb{Q}}$, Galois-equivariance of its point-place bijection for `arithmeticGalois`, and compatibility of its places with those of $M_0$ under $\overline{\mathbb{Q}}\otimes_{\mathbb{Q}}F_N\cong\overline{F}_N$; for each valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit in $A$, a lift $\rho_A\colon R\to A$ of $R\to\overline{\mathbb{Q}}$, a curve model $M_A$ over the residue field of $A$ of `modularFunctionFieldFullC` with an isomorphism onto the corresponding base change of $X$, and, when that residue field is algebraically closed, a place-reduction map `IsPlaceReductionModL` compatible with the three point-place bijections; finally a point $s$ of $\operatorname{Spec}R$ with $\{s\}$ closed, a specialisation $(e_0\circ\mathrm{pr}_1)(x_0)\rightsquigarrow\varepsilon_\infty(s)$, a ring retraction $\pi$ of the stalk of $X$ at $\varepsilon_\infty(s)$ onto $R$ splitting the structure germs and with $\ker(\text{stalk map of }\varepsilon_\infty\text{ at }s)\le\ker\pi$, and an element $t_0$ of that stalk with $\pi t_0=0$ and $\ker\pi\le (t_0)+(\ker\pi)^2$. The conclusion: there is a unit $g$ in the stalk of $X$ at $(e_0\circ\mathrm{pr}_1)(x_0)$ such that the image of $g$ times the specialisation of $t_0$, transported by the stalk map of $e_0\circ\mathrm{pr}_1$ at $x_0$ into the stalk of $M_0.C$, then into the function field and back to $F_N$ by $M_0.\mathrm{ffEquiv}^{-1}$, equals $j^{-1}$ in $\mathbb{Q}((q))$.
--
--   This records that a parameter $t_0$ cutting out the cusp section $\varepsilon_\infty$ of the $p$-integral model of $X_0(N)$ restricts, at the generic point of that section, to a uniformiser of the place $\infty$ of the modular function field, normalised so that its $q$-expansion is exactly $1/j$ up to a unit; the point is that the cusp $\infty$ of $\Gamma_0(N)$ has width $1$, so $\operatorname{ord}_\infty(1/j)=1$. It feeds the construction of a power-series parameter and a retraction at the cusp, used in the $q$-expansion analysis of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_mul_stalkSpecializes_eq_jq_inv_cuspSection_of_ratCurveModel_compat_of_neZero.lean

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

theorem ModularCurve.exists_isUnit_stalk_ffEquiv_symm_stalkMap_mul_stalkSpecializes_eq_jq_inv_cuspSection_of_ratCurveModel_compat_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c]

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)

    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)
    (x₀ : closedPoints M₀.C)
    (y : Spec (CommRingCat.of ℚ) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
    (hx₀ : M₀.placeOfPoint x₀ = cuspInftyFull N)
    (hy : y ≫ pullback.snd c _ = 𝟙 _)
    (hyε : y ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) ≫ εinf.1)
    (hyx₀ : (y ≫ inv e₀).base (IsLocalRing.closedPoint ℚ) = x₀.1)

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
    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N),
        IsPlaceReductionModL A N r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))

    (s : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) (hs : IsClosed ({s} : Set (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))))
    (hspec : (e₀ ≫ pullback.fst c _).base x₀.1 ⤳ εinf.1.base s)

    (π : X.presheaf.stalk (εinf.1.base s) →+* ↥(GaloisRep.ratLocalizedAt p))
    (hπι : ∀ r : ↥(GaloisRep.ratLocalizedAt p), π ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r))) = r)
    (hπker : RingHom.ker (Scheme.Hom.stalkMap εinf.1 s).hom ≤ RingHom.ker π)
    (t₀ : X.presheaf.stalk (εinf.1.base s)) (ht₀ : π t₀ = 0) (hcot : RingHom.ker π ≤ Ideal.span {t₀} ⊔ RingHom.ker π ^ 2) :
    ∃ g : X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x₀.1), IsUnit g ∧
      ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom (g * (X.presheaf.stalkSpecializes hspec).hom t₀))) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) = (jq : LaurentSeries ℚ)⁻¹ := by sorry
