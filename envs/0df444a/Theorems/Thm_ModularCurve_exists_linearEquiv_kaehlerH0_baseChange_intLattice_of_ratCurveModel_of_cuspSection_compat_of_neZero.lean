-- Prove2me | Theorems.Thm_ModularCurve_exists_linearEquiv_kaehlerH0_baseChange_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
-- name    : ModularCurve.exists_linearEquiv_kaehlerH0_baseChange_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/431e87ec-fc98-5250-8f0c-781f1e9f737b
-- title:
--   Global 1-forms of the ℤ₍ₚ₎-model versus p-integral cusp forms
-- statement:
--   Fix $N\ge 1$, a prime $p$ with $p\nmid N$, and a ring embedding $\iota_0:\overline{\mathbf Q}\to\mathbf C$; write $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of rationals whose denominator is coprime to $p$. Let $c:X\to\operatorname{Spec}R$ be proper and smooth of relative dimension $1$ with $X$ integral, and $\mathcal V$ a cover of $X$ by two affine opens $U_0,U_1$ with $U_0\cap U_1$ affine; $H^0$ denotes the kernel of the Čech differential $\Omega_{\Gamma(U_0)/R}\oplus\Omega_{\Gamma(U_1)/R}\to\Omega_{\Gamma(U_0\cap U_1)/R}$. Further data: a curve model $M_0$ over $\mathbf Q$ of $F_N=$ `modularFunctionFieldFull N` $\subset\mathbf Q((q))$ (an integral proper smooth curve with a bijection of closed points onto places, matching stalks with valuation subrings) together with an isomorphism $e_0$ onto the generic fibre $X\times_R\mathbf Q$ over $\operatorname{Spec}\mathbf Q$, whose generic point lies over $U_0$ and over $U_0\cap U_1$; a ring map $\iota:\Gamma(X,U_0)\to\bar F_N=$ `modularFunctionFieldBar N` which, coefficientwise over $\mathbf Q\to\overline{\mathbf Q}$, is pullback along $e_0$ followed by the germ at the generic point and $M_0.\mathrm{ffEquiv}^{-1}$, and which is $R$-semilinear over $R\to\overline{\mathbf Q}$; an additive map $\mathrm{res}$ on $H^0$ sending $\omega$ to the image of its first component under [`KaehlerDifferential.mapOfRingHom`](def/AlgebraicGeometry_TwoAffineOpenCoverKaehler.html#L16) along $\iota$; a section $\varepsilon_\infty$ of $c$, a closed point $x_0$ of $M_0$ at the cusp $\infty$ (the place `cuspInftyFull N`) and a rational point $y$ of the generic fibre lying on $\varepsilon_\infty$ and mapping to $x_0$; a curve model $M_\eta$ over $\overline{\mathbf Q}$ of $\bar F_N$ identified with $X\times_R\overline{\mathbf Q}$, assumed Galois-compatible (`hgal`: conjugate $\overline{\mathbf Q}$-points have places translated by the semilinear action `arithmeticGalois`) and place-compatible with $M_0$ (`hcompat`: the valuation subring of the place of a $\overline{\mathbf Q}$-point, pulled back along $F_N\to\overline{\mathbf Q}\otimes_{\mathbf Q}F_N\cong\bar F_N$, is that of the place of the closed point of $M_0$ beneath it); and, for every valuation subring $A$ of $\overline{\mathbf Q}$ with $p$ a non-unit, a lift $\rho_A:R\to A$ of $R\to\overline{\mathbf Q}$, a curve model $M_A$ over the residue field of $A$ of `modularFunctionFieldFullC` identified with $X\times_R\kappa(A)$, and (when $\kappa(A)$ is algebraically closed) a place-reduction map $r$ satisfying `IsPlaceReductionModL` and compatible with specialisation of points through $\operatorname{Spec}A\to X$. The conclusion is that $\mathrm{res}$ is injective and that there is an $R$-linear isomorphism $\Theta:H^0\xrightarrow{\ \sim\ }R\otimes_{\mathbf Z}S_2(\Gamma_0(N))_{\mathbf Z}$, where $S_2(\Gamma_0(N))_{\mathbf Z}=$ [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3) is the $\mathbf Z$-span of the weight-$2$ cusp forms with integral $q$-coefficients, such that: whenever $\Theta\omega=1\otimes f$, the $\iota_0$-image of the $q$-expansion `diffQExpBar N (res ω)` is the $q$-expansion of $f$; and for every prime $\ell$ and every $\omega$ there is $\omega'\in H^0$ with $\mathrm{res}\,\omega'=$ `heckeDiffBar N ℓ (res ω)` and $\Theta\omega'$ the base change to $R$ of the lattice Hecke operator `latticeRestrictHom N ∅ (heckeProj N (heckeGen ℓ))` applied to $\Theta\omega$.
--
--   This is the integral comparison between the global relative $1$-forms of a $\mathbf Z_{(p)}$-model of $X_0(N)$ and the $p$-integral weight-$2$ cusp forms of level $N$, in a form that records Hecke equivariance and the compatibility of the rational, geometric and mod-$\ell$ models through their places. It feeds the construction of the relative Jacobian and its Hecke module structure, being used by [`ModularCurve.exists_pts_relJacobian_jZero_level_dualNumber_kernel_equiv_addMonoidHom_intLattice_latticeHeckeFamily_integral_of_representsRelSubPic_of_ratCurveModel_of_not_dvd`](thm.html#ModularCurve.exists_pts_relJacobian_jZero_level_dualNumber_kernel_equiv_addMonoidHom_intLattice_latticeHeckeFamily_integral_of_representsRelSubPic_of_ratCurveModel_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearEquiv_kaehlerH0_baseChange_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero.lean

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

theorem ModularCurve.exists_linearEquiv_kaehlerH0_baseChange_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)
    (hgen01 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))

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
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x)) :
    Function.Injective res ∧
    ∃ Θ : ↥((𝒱.kaehlerSections c).H0) ≃ₗ[↥(GaloisRep.ratLocalizedAt p)] (↥(GaloisRep.ratLocalizedAt p) ⊗[ℤ] ↥(CuspForm.intLattice N 2)),
      (∀ (ω : ↥((𝒱.kaehlerSections c).H0)) (f : ↥(CuspForm.intLattice N 2)), Θ ω = (1 : ↥(GaloisRep.ratLocalizedAt p)) ⊗ₜ[ℤ] f →
        coeffMap ι₀ (diffQExpBar N (res ω)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2))) ∧
      (∀ (ℓ : Nat.Primes) (ω : ↥((𝒱.kaehlerSections c).H0)), ∃ ω' : ↥((𝒱.kaehlerSections c).H0),
        res ω' = heckeDiffBar N ℓ (res ω) ∧
        Θ ω' = ((((CuspForm.latticeRestrictHom N ∅).toRingHom.comp (heckeProj N)) (heckeGen ℓ)).val).baseChange ↥(GaloisRep.ratLocalizedAt p) (Θ ω)) := by sorry
