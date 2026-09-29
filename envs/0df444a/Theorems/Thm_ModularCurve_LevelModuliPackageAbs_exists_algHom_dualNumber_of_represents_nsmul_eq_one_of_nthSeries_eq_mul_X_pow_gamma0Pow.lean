-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/53938e39-caa0-5e95-a8ce-4e85270c2772
-- title:
--   One-dimensional tangent space at an ordinary q-torsion point
-- statement:
--   Fix a prime $q$, a prime $\ell\ge 3$, a nonzero natural number $M'$, and a commutative ring $A_0$, together with hypotheses `hℓ` and `hM` asserting that Katz level-$\ell$ data (two points satisfying the Weierstrass equation, killed by $\mathrm{pre}\Psi_\ell$, with invertible independence elements) and the prime-power generator-kernel conditions `IsGamma0PowAt` are transported along Weierstrass variable changes. Let $\mathcal{G}$ be a family of relative group laws on the projective models of curves with unit discriminant over $A_0$-algebras, chord-tangent (compatible, via some identification of field-valued sections with affine points, with addition and Galois twisting) and with identity section given by a chart homomorphism sending $x/y$ and $z/y$ to $0$. Let `Pet` be a fine moduli package for the moduli datum of the rigid Weierstrass data with level component the product of `gamma0PowComponent A₀ M' hM`, `levelPComponent A₀ ℓ hℓ` and the trivial component, and let $x$ be a raw datum over $B_0=$ `Pet.B₀` (a curve with unit discriminant plus level data) whose class is the universal point. Let $C$ be a $B_0$- and compatibly $A_0$-algebra, and $Qu$ a section of the projective model of $x$'s curve over $\operatorname{Spec} C$ with $q\cdot Qu$ the identity, such that $(C,Qu)$ universally represents $q$-torsion sections: for every $B_0$-algebra $T$, a section $Q$ over $T$ is killed by $q$ precisely when it is $Qu$ composed with $\operatorname{Spec}$ of a unique $B_0$-algebra map $C\to T$. Let $R$ be a Noetherian local ring, complete for its maximal ideal, an $A_0$-algebra with an $A_0$-algebra map $\iota:C\to R$; let $k$ be a field of characteristic $q$ in which $\ell$ and $M'$ are nonzero, $\mathrm{res}_R:R\to k$ surjective with kernel the maximal ideal; let $W_0$ be a complete discrete valuation ring with maximal ideal $(q)$ and residue map $\mathrm{res}_0:W_0\to k$, with $R$ a $W_0$-algebra compatibly over $A_0$ and $\mathrm{res}_R$ extending $\mathrm{res}_0$. Assume the universal property `hfac`: every $A_0$-algebra map $C\to T$ into an Artinian local $W_0$-algebra $T$ with residue field $k$ compatible with $\mathrm{res}_0$, lifting $\mathrm{res}_R\circ\iota$ modulo the maximal ideal, extends uniquely to a $W_0$-algebra map $R\to T$ compatible with the residue maps. Finally let $F_0$ be a formal group over $k$ whose power series is the fixed formal group law of the curve base-changed along $\mathrm{res}_R\circ\iota$, assume $F_0$'s $q$-th iterated series is a unit times $X^q$ (ordinarity), and assume the reduction of $Qu$ along $\mathrm{res}_R\circ\iota$ is not the identity section. Then there exists a $W_0$-algebra homomorphism $\Phi_1:R\to \kappa[\varepsilon]$, $\kappa$ the residue field of $R$, whose constant component is the residue map and whose $\varepsilon$-component is not identically zero, such that every $W_0$-algebra homomorphism $\Phi:R\to\kappa[\varepsilon]$ with constant component the residue map has $\varepsilon$-component a fixed scalar multiple of that of $\Phi_1$.
--
--   This is the first-order (tangent space) step in the Serre–Tate style analysis of the ring $R$ attached to a $q$-torsion section on the universal curve with $\Gamma_0(M')$-type generator-kernel data and Katz level-$\ell$ structure: at an ordinary point with non-trivial torsion section the relative tangent space of $R$ over $W_0$ is one-dimensional. It is used to identify $R$ with a power series ring over $W_0$ in the subsequent structure theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_gamma0Pow.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
  AlgebraicGeometry CategoryTheory NeronModelInfra
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_gamma0Pow
    (q : ℕ) [Fact q.Prime] (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)

    (Pet : LevelModuliPackageAbs A₀
      (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).toLevelModuliDatum)
    (x : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Raw Pet.B₀)
    (hx : (Quot.mk _ x :
      (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Pt Pet.B₀) = Pet.univ)

    (C : Type) [CommRing C] [Algebra Pet.B₀ C] [Algebra A₀ C] [IsScalarTower A₀ Pet.B₀ C]
    (Qu : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ C))) (projModelStrCR x.curve))
    (hQu : (𝒢 Pet.B₀ x.curve x.isUnit_Δ).nsmul _ q Qu = (𝒢 Pet.B₀ x.curve x.isUnit_Δ).one _)
    (hrep : ∀ (T : Type) [CommRing T] [Algebra Pet.B₀ T]
        (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ T))) (projModelStrCR x.curve)),
        (𝒢 Pet.B₀ x.curve x.isUnit_Δ).nsmul _ q Q = (𝒢 Pet.B₀ x.curve x.isUnit_Δ).one _ ↔
          ∃! ψ : C →ₐ[Pet.B₀] T, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Qu.1 = Q.1)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : C →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓ : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    [Algebra W₀ R] [Algebra A₀ W₀] [IsScalarTower A₀ W₀ R]
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)
    (hfac : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : C →ₐ[A₀] T, (∀ c : C, resT (φ c) = resR (ι c)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ c : C, Φ (ι c) = φ c)

    (F₀ : FormalGroup k)
    (hF₀W : F₀.toPowerSeries =
      ((x.curve).map ((resR.comp ι.toRingHom).comp (algebraMap Pet.B₀ C))).formalGroupLawFixed)
    (hF₀ : ∃ u : PowerSeries k, IsUnit u ∧ F₀.nthSeries q = u * PowerSeries.X ^ q)

    (hQ0 : Spec.map (CommRingCat.ofHom (resR.comp ι.toRingHom)) ≫ Qu.1 ≠
      ((𝒢 Pet.B₀ x.curve x.isUnit_Δ).one
        (Spec.map (CommRingCat.ofHom ((resR.comp ι.toRingHom).comp (algebraMap Pet.B₀ C))))).1) :
    ∃ Φ₁ : R →ₐ[W₀] DualNumber (ResidueField R),
      (∀ r : R, (Φ₁ r).fst = residue R r) ∧ (∃ r : R, (Φ₁ r).snd ≠ 0) ∧
      ∀ Φ : R →ₐ[W₀] DualNumber (ResidueField R), (∀ r : R, (Φ r).fst = residue R r) →
        ∃ c : ResidueField R, ∀ r : R, (Φ r).snd = c * (Φ₁ r).snd := by sorry
