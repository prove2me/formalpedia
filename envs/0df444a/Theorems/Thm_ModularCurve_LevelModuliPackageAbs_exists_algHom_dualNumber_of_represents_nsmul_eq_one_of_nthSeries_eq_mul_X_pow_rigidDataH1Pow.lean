-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/dc3f3ba8-42e6-5f1a-acee-99efcc7056e1
-- title:
--   First-order deformations with q-torsion section form a line (H₁ level)
-- statement:
--   Fix a prime $q$, a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$, a nonzero natural number $M'$, and a commutative ring $A_0$, together with three transport hypotheses, valid over all $A_0$-algebras $T$ and all Weierstrass variable changes $C$: `hℓ`, that `IsGamma1Point W ℓg D` (the point $(x_P,y_P)$ satisfies the affine equation, $(\mathrm{pre}\Psi_{\ell_g})(x_P)=0$, and $(x_Q,y_Q)=(x_P,y_P)$) is preserved by the simultaneous change of $W$ and $D$; `hM`, that `IsGamma0PowAt W p k h` is preserved when $h$ is replaced by `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and `hL`, that a divisibility $h \mid$ `inLineMulPoly W ℓg n x` transports likewise. Let $\mathcal G$ be a family of relative group laws on the projective models of Weierstrass curves with unit discriminant over $A_0$-algebras, assumed chord–tangent (`IsChordTangent`) and with the origin as identity (`IsOriginIdentity`). Let $L$ be the level component obtained from the product of `gamma0PowComponent A₀ M' hM` (tuples of prime-power generator-kernel polynomials, one for each prime factor of $M'$), `gamma1Component A₀ ℓg hℓ` (level-$P$ data with a $\Gamma_1(\ell_g)$-point) and the trivial component, restricted along the link condition `IsGamma1Link W ℓg M' h D`, and let `Pet` be a fine moduli package for the associated level moduli datum: a ring $B_0 =$ `Pet.B₀` with a universal point `Pet.univ` representing the functor of raw data (curve with unit discriminant and level structure) modulo variable change. Let $x$ be a raw datum over $B_0$ whose class is `Pet.univ`. Let $C$ be a commutative $B_0$- and $A_0$-algebra with compatible tower, and $Qu$ a $C$-point of the projective model of $x$`.curve` over $\operatorname{Spec} B_0$ with $q \cdot Qu$ the identity section, which is universal with this property: for every $B_0$-algebra $T$, a $T$-point $Q$ satisfies $q \cdot Q = 0$ exactly when it factors through $Qu$ along a unique $B_0$-algebra map $C \to T$. Let $R$ be a noetherian local ring, complete for its maximal ideal, an $A_0$-algebra equipped with $\iota : C \to R$ over $A_0$; let $k$ be a field of characteristic $q$ in which $\ell_g$ and $M'$ are invertible, $\mathrm{res}_R : R \to k$ a surjection with kernel the maximal ideal; let $W_0$ be a complete discrete valuation domain with maximal ideal $(q)$ and residue map $\mathrm{res}_0 : W_0 \to k$, with $R$ a $W_0$-algebra compatibly with $A_0 \to W_0 \to R$ and $\mathrm{res}_R$ extending $\mathrm{res}_0$. Assume `hfac`: for every artinian local $W_0$- and $A_0$-algebra $T$ with compatible residue map onto $k$, every $A_0$-algebra map $\varphi : C \to T$ lifting $\mathrm{res}_R \circ \iota$ extends to a unique $W_0$-algebra map $\Phi : R \to T$ inducing the identity on residue fields and satisfying $\Phi \circ \iota = \varphi$. Assume further that a formal group $F_0$ over $k$ has power series equal to `formalGroupLawFixed` of $x$`.curve` base-changed along $\mathrm{res}_R \circ \iota$, that its $q$-th series `nthSeries q` equals a unit times $X^q$, and that the reduction of $Qu$ to $k$ is not the identity section. The conclusion: there is a $W_0$-algebra homomorphism $\Phi_1 : R \to (\operatorname{ResidueField} R)[\varepsilon]$ whose first component is the residue map, whose second component is not identically zero, and such that every $W_0$-algebra homomorphism $\Phi : R \to (\operatorname{ResidueField} R)[\varepsilon]$ with first component the residue map has second component equal to $c$ times that of $\Phi_1$ for some scalar $c$ in the residue field.
--
--   This is the tangent-space computation for the complete local ring $R$ of the $q$-torsion covering at an ordinary point with non-trivial $q$-torsion section, in the level-$H_1$ setting ($\Gamma_0(M') \cap \Gamma_1(\ell_g)$-structure with link condition): the space of first-order deformations over $W_0$ is a line. It is used in the identification of $R$ with a ring of the form obtained by adjoining a root to a power series ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_rigidDataH1Pow.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
  AlgebraicGeometry CategoryTheory NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) [NeZero M']
    (A₀ : Type) [CommRing A₀]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)

    (Pet : LevelModuliPackageAbs A₀
      ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓg hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum)
    (x : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓg hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Raw Pet.B₀)
    (hx : (Quot.mk _ x :
      ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓg hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Pt Pet.B₀) = Pet.univ)

    (C : Type) [CommRing C] [Algebra Pet.B₀ C] [Algebra A₀ C] [IsScalarTower A₀ Pet.B₀ C]
    (Qu : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ C))) (projModelStrCR x.curve))
    (hQu : (𝒢 Pet.B₀ x.curve x.isUnit_Δ).nsmul _ q Qu = (𝒢 Pet.B₀ x.curve x.isUnit_Δ).one _)
    (hrep : ∀ (T : Type) [CommRing T] [Algebra Pet.B₀ T]
        (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ T))) (projModelStrCR x.curve)),
        (𝒢 Pet.B₀ x.curve x.isUnit_Δ).nsmul _ q Q = (𝒢 Pet.B₀ x.curve x.isUnit_Δ).one _ ↔
          ∃! ψ : C →ₐ[Pet.B₀] T, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Qu.1 = Q.1)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : C →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓg : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
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
