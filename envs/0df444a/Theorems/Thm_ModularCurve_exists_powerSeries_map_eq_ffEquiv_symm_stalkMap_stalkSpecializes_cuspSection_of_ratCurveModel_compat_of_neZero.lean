-- Prove2me | Theorems.Thm_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero
-- name    : ModularCurve.exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/f8f20436-f5c3-5036-af99-a9068b57ac4a
-- title:
--   Integral q-expansions of germs at the cusp of a ℤ₍ₚ₎-model
-- statement:
--   Fix $N\ge 1$ and a prime $p$ with $p\nmid N$, and write $R=\mathrm{ratLocalizedAt}\ p$ for the subring of $\mathbf{Q}$ of rationals whose denominator is coprime to $p$. Let $c\colon X\to\operatorname{Spec}R$ be proper and smooth of relative dimension $1$ with $X$ integral. The data are: a curve model $M_0$ over $\mathbf{Q}$ of the field $F_N=$ `modularFunctionFieldFull N` (the subfield of $\mathbf{Q}((q))$ generated over $\mathbf{Q}$ by the expansions $\mathrm{qExpand}\ \mathbf{Q}\ d\ jq$ for $d\mid N$), together with an isomorphism $e_0$ from $M_0.C$ onto the pullback of $c$ along $\operatorname{Spec}$ of $R\to\mathbf{Q}$ commuting with the structure maps; a section $\varepsilon_\infty$ of $c$; a closed point $x_0$ of $M_0.C$ whose place is `cuspInftyFull N`, and a $\mathbf{Q}$-point $y$ of the pullback which is a section over $\operatorname{Spec}\mathbf{Q}$, lies over $\varepsilon_\infty$ after base change, and maps to $x_0$ under $\operatorname{inv} e_0$; a curve model $M_\eta$ over $\overline{\mathbf{Q}}$ of `modularFunctionFieldBar N` with an analogous isomorphism $e_\eta$, satisfying Galois equivariance of $\mathrm{pointEquivPlace}$ for the coefficientwise action `arithmeticGalois` and compatibility of the places of $M_\eta$ with those of $M_0$ under contraction along $F_N\to\overline{\mathbf{Q}}\otimes_{\mathbf{Q}}F_N\cong$ `modularFunctionFieldBar N`; and, for every valuation subring $A$ of $\overline{\mathbf{Q}}$ with $p$ a nonunit in $A$, a lift $\rho_A\colon R\to A$ of $R\to\overline{\mathbf{Q}}$, a curve model $M_s(A)$ over the residue field of $A$ of `modularFunctionFieldFullC (ResidueField A) N` isomorphic to the corresponding pullback of $c$, and (when that residue field is algebraically closed) a place-reduction map $r$ in the sense of `IsPlaceReductionModL` compatible with specialisation of points of $X$ over $\rho_A$. Finally let $s$ be a closed point of $\operatorname{Spec}R$ such that the image of $x_0$ under $e_0$ followed by the first projection specialises to $\varepsilon_\infty(s)$, and let $z$ be a germ in the stalk of $X$ at $\varepsilon_\infty(s)$. Then there is a power series $P\in R[[q]]$ such that the image of $z$ under specialisation to the stalk at the image of $x_0$, the stalk map of $e_0$ followed by the first projection, the inclusion of the local ring of $M_0.C$ at $x_0$ into the function field, and $M_0.\mathrm{ffEquiv}^{-1}$, viewed as an element of $\mathbf{Q}((q))$, equals the Laurent series attached to $P$ with coefficients mapped into $\mathbf{Q}$.
--
--   This is the integral $q$-expansion principle in weight $0$: a function regular at the special point of the cusp of an integral model of $X_0(N)$ over $\mathbf{Z}_{(p)}$ has $q$-expansion with coefficients in $\mathbf{Z}_{(p)}$. It feeds the corresponding integral comparison for differentials, being cited by [`ModularCurve.exists_powerSeries_diffQExpBar_eq_ofPowerSeries_map_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero`](thm.html#ModularCurve.exists_powerSeries_diffQExpBar_eq_ofPowerSeries_map_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero) and by [`ModularCurve.exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero`](thm.html#ModularCurve.exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero.lean

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing CuspForm
open ModularCurve

theorem ModularCurve.exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero
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
    (z : X.presheaf.stalk (εinf.1.base s)) :
    ∃ P : PowerSeries ↥(GaloisRep.ratLocalizedAt p),
      ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom z))) :
          ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
        HahnSeries.ofPowerSeries ℤ ℚ (P.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) := by sorry
