-- Prove2me | Theorems.Thm_ModularCurve_ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero
-- name    : ModularCurve.ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/577a5d4e-be75-51fa-9e97-d53c8c8a41ed
-- title:
--   An A-point with j∈mathfrak m_A reduces to a zero of ̄ j
-- statement:
--   Fix $N\ge 1$, a prime $p$ with $p\nmid N$, and an integral scheme $X$ proper and smooth of relative dimension $1$ over $\operatorname{Spec}$ of the subring $\mathbb{Z}_{(p)}$ of rationals whose denominator is coprime to $p$. The data are: a curve model $M_0$ over $\mathbb{Q}$ of the field $\mathbb{Q}(q\text{-expansions } j(q^d),\,d\mid N)$ together with an isomorphism $e_0$ onto the rational fibre of $c$ over the structure map; a section $\varepsilon_\infty$ of $c$, a closed point $x_0$ of $M_0.C$ whose place is the $q$-adic cusp at infinity, and a $\mathbb{Q}$-point $y$ of the rational fibre factoring through $\varepsilon_\infty$ and carrying the closed point of $\mathbb{Q}$ to $x_0$; a curve model $M_\eta$ over $\overline{\mathbb{Q}}$ of the Laurent base change of that field, isomorphic via $e_\eta$ to the geometric generic fibre, with Galois equivariance of the bijection $\mathrm{pointEquivPlace}$ between $\overline{\mathbb{Q}}$-points and places, and compatibility of those places with the places of $M_0$ under restriction along the base-change embedding; for each valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p\in A.\mathrm{nonunits}$, a lift $\rho(A)$ of $\mathbb{Z}_{(p)}\to\overline{\mathbb{Q}}$ through $A$, a curve model $M_s(A)$ over the residue field of $A$ of the corresponding function field, isomorphic to the fibre of $c$ along $\mathrm{residue}\circ\rho(A)$, and, when the residue field is algebraically closed, a reduction map on places as below; finally a closed point $s$ of the base with $(e_0\ggg \mathrm{fst})(x_0)$ specialising to $\varepsilon_\infty(s)$. Fix moreover such an $A$ whose residue field is algebraically closed of characteristic $p$, and a map $r$ from places of the geometric function field to places of the reduced one satisfying `IsPlaceReductionModL`: $r$ preserves degrees of places, and for a Laurent series with coefficients in $A$ lying in the geometric function field and with nonzero reduction lying in the reduced function field, the pushforward along $r$ of its divisor is the divisor of the reduced series; $r$ is also assumed compatible with reduction of points, in the sense that whenever an $A$-point of $X$ restricts to a $\overline{\mathbb{Q}}$-point of $M_\eta$ and reduces to a residue-field point of $M_s(A)$, the place of the latter is $r$ of the place of the former. Let $x_A$ be an $A$-point of $X$ over $\operatorname{Spec}\rho(A)$, let $x$ be a $\overline{\mathbb{Q}}$-point of $M_\eta$ whose image in $X$ is the restriction of $x_A$, and let $g$ be a germ of $\mathcal{O}_X$ at the image of the closed point of $A$ under $x_A$ such that the pullback of $g$ along $x_A$ lies in the maximal ideal of $A$; assume the image of the generic point of $M_0.C$ specialises to that point, and that transporting $g$ to the function field of $M_0.C$ (via the specialisation map, the stalk map of $e_0$ followed by the first projection, and $M_0.\mathrm{ffEquiv}^{-1}$) gives exactly $j(q)$. Then the order of $q^{-1}E_4^3\eta^{-24} \bmod \mathfrak m_A$, viewed in the function field over the residue field of $A$, at the place $r(\mathrm{pointEquivPlace}(x))$ is strictly positive.
--
--   This is the first of the two Deuring clauses on reduction of places: a point of the $\mathbb{Z}_{(p)}$-model of $X_0(N)$ at which the modular function $j$ takes a value in the maximal ideal of $A$ reduces to a zero of $\bar j$ on the special fibre. It is used in the argument ruling out a vertical component through the cusp, namely by [`ModularCurve.false_of_pow_mul_ffEquiv_symm_stalkMap_stalkSpecializes_eq_jq_mul_cuspSection_of_ratCurveModel_compat_of_neZero`](thm.html#ModularCurve.false_of_pow_mul_ffEquiv_symm_stalkMap_stalkSpecializes_eq_jq_mul_cuspSection_of_ratCurveModel_compat_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero.lean

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

theorem ModularCurve.ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero
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
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hr : IsPlaceReductionModL A N r)
    (hrsp : ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))
    (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
    (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hx : x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1)
    (g : X.presheaf.stalk (xA.1.base (IsLocalRing.closedPoint ↥A)))
    (hg : (Scheme.stalkClosedPointTo xA.1).hom g ∈ IsLocalRing.maximalIdeal ↥A)
    (hgenP : (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).base (genericPoint M₀.C) ⤳ xA.1.base (IsLocalRing.closedPoint ↥A))
    (hgj : M₀.ffEquiv.symm ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) (genericPoint M₀.C)).hom
        ((X.presheaf.stalkSpecializes hgenP).hom g)) = ⟨jq, modularFunctionField_le_full N (jq_mem N)⟩) :
    0 < (r (Mη.pointEquivPlace x)).ord
        (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩ : modularFunctionFieldFullC (ResidueField ↥A) N) := by sorry
