-- Prove2me | Theorems.Thm_ModularCurve_exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
-- name    : ModularCurve.exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/44597c36-9b90-569d-a70e-ccdae52ef8c1
-- title:
--   Integral weight-two cusp forms as relative differentials on the model
-- statement:
--   Fix $N\ge 1$, a prime $p$ with $p\nmid N$, and an embedding $\iota_0\colon\overline{\mathbf Q}\to\mathbf C$. Let $R$ be the subring $\mathrm{ratLocalizedAt}\,p$ of $\mathbf Q$ of fractions whose denominator is coprime to $p$, let $c\colon X\to\operatorname{Spec}R$ be proper and smooth of relative dimension $1$ with $X$ integral, and let $\mathcal V$ be a cover of $X$ by two affine opens $U_0,U_1$ with affine intersection and $U_0\sqcup U_1=\top$. The data are: a `CurveModel` $M_0$ over $\mathbf Q$ of the modular function field $F_N=\mathbf Q(j(q^d):d\mid N)\subset\mathbf Q((q))$ together with an isomorphism $e_0$ onto the fibre $X_{\mathbf Q}$ over the structure maps, the generic point of $M_0$ lying in the preimage of $U_0$; a ring map $\iota\colon\Gamma(X,U_0)\to\bar F_N$ (the field generated over $\overline{\mathbf Q}$ inside $\overline{\mathbf Q}((q))$ by the coefficientwise image of $F_N$) given on each section by the Laurent expansion of its germ at the generic point of $M_0$, and agreeing with $R\to\overline{\mathbf Q}$ on constants; an additive map $\mathrm{res}$ on $H^0$ of the two-chart Kähler sections (the kernel of the Čech difference on $\Omega_{\Gamma(U_0)/R}\times\Omega_{\Gamma(U_1)/R}$) sending $\omega$ to the image of its $U_0$-component under the semilinear map $\Omega_{\Gamma(U_0)/R}\to\Omega_{\bar F_N/\overline{\mathbf Q}}$ induced by $\iota$; a section $\varepsilon_\infty$ of $c$ over $\operatorname{Spec}R$ whose associated $\mathbf Q$-point $y$ corresponds under $e_0^{-1}$ to a closed point $x_0$ of $M_0$ whose place is the $q$-adic cusp $\mathrm{cuspInftyFull}\,N$; a `CurveModel` $M_\eta$ over $\overline{\mathbf Q}$ of $\bar F_N$ with an isomorphism $e_\eta$ onto $X_{\overline{\mathbf Q}}$, whose places transform under $\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$-translation of $\overline{\mathbf Q}$-points by the semilinear action $\mathrm{arithmeticGalois}$ (hypothesis `hgal`) and whose places restrict along $F_N\hookrightarrow\overline{\mathbf Q}\otimes_{\mathbf Q}F_N\cong\bar F_N$ to the corresponding places of $M_0$ (hypothesis `hcompat`); and, for each valuation subring $A$ of $\overline{\mathbf Q}$ with $p$ in its nonunits, lifts $\rho_A\colon R\to A$ of $R\to\overline{\mathbf Q}$, curve models $M_A$ over the residue field of $A$ of the corresponding modular function field there, isomorphic to the fibre of $c$ along $A\to\kappa(A)$, and, when $\kappa(A)$ is algebraically closed, a degree-preserving place-reduction map $r$ satisfying `IsPlaceReductionModL` and matching the places of $\overline{\mathbf Q}$-points of $M_\eta$ with those of their reductions (hypothesis `hsp`). Then for every $f$ in $\mathrm{CuspForm.intLattice}\,N\,2$, the $\mathbf Z$-span of the weight-two cusp forms on $\Gamma_0(N)$ all of whose $q$-expansion coefficients are rational integers, there exists $\omega\in H^0$ of the Kähler sections such that applying $\iota_0$ coefficientwise to the $q$-expansion $\mathrm{diffQExpBar}\,N(\mathrm{res}\,\omega)$ yields exactly the Laurent series attached to the $q$-expansion of $f$ of width $1$.
--
--   This is the surjectivity half of the integral $q$-expansion principle for weight-two forms on $\Gamma_0(N)$ with $p\nmid N$: every cusp form with integral Fourier coefficients is realised by a relative $1$-form on the smooth proper $\mathbf Z_{(p)}$-model, with no auxiliary power of $p$ — a strengthening of the companion statement that produces such an $\omega$ only after scaling by a power of $p$, which together with the integrality criterion for the lattice is what this statement cites. It feeds the construction of the linear equivalence between the module of global relative differentials on the model and the base change of the integral cusp-form lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero.lean

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

theorem ModularCurve.exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)

    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N))
    (hιdef : ∀ a : (𝒱.cover c).A0, ((ι a : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) (genericPoint M₀.C) hgen0).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0)).hom a))) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR ω.val.1)

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
    (f : ↥(CuspForm.intLattice N 2)) :
    ∃ ω : ↥((𝒱.kaehlerSections c).H0),
      coeffMap ι₀ (diffQExpBar N (res ω)) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := by sorry
