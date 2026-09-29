-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_nonempty_algEquiv_adjoinRoot_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.nonempty_algEquiv_adjoinRoot_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/f46faec3-e057-5516-ad82-566d89d1fc39
-- title:
--   Completed local ring at level H₁ is S[X]/(g)
-- statement:
--   Fix a prime $q$, natural numbers $\ell_g$ and $M'$ with $\ell_g$ prime, $\ell_g \equiv 11 \pmod{12}$ and $M' \neq 0$, and a commutative ring $A_0$.
--
--   **Transport hypotheses over $A_0$.** Three hypotheses assert compatibility of the level conditions with Weierstrass variable changes, uniformly in an $A_0$-algebra $T$, a curve $W/T$ and a change of variables $C$: `hℓ` says that if a `LevelPData` $D = (x_P,y_P,x_Q,y_Q)$ satisfies [`ModularCurve.IsGamma1Point W ℓg D`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) (that is, $(x_P,y_P)$ lies on the affine equation of $W$, the division polynomial $W.\mathrm{preΨ}\,\ell_g$ vanishes at $x_P$, and $x_Q = x_P$, $y_Q = y_P$) then $D.\mathrm{variableChange}\,C$ satisfies the same condition for $C \bullet W$; `hM` says that [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) (for $p^k = 2$ the condition `IsTwoKernel`, otherwise `IsCyclicGenKernel p k`) is preserved by $h \mapsto$ [`ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h`](def/ModularCurve_WeierstrassLevelComponents.html#L104); `hL` says that a divisibility $h \mid \mathrm{ModularCurve.inLineMulPoly}\ W\ \ell_g\ n\ x$ implies $\mathrm{ModularCurve.kernelVariableChangeDeg}\ C\ d\ h \mid \mathrm{ModularCurve.inLineMulPoly}\ (C \bullet W)\ \ell_g\ n\ (u^{-2}(x - r))$ with $u,r$ the components of $C$.
--
--   **Group-law data.** $\mathcal G$ is a family `GroupLaws A₀` of relative group laws on the projective models of curves with unit discriminant over $A_0$-algebras, assumed chord–tangent (`h𝒢`: each law admits a points-evaluation `IsPointsEval`) and origin-normalised (`h𝒢O`: each identity section is cut out by a ring homomorphism from the origin chart killing $x/y$ and $z/y$), and $\mathcal T$ is a `LevelTransport A₀ 𝒢 q` whose functorialities are section-compatible (`h𝒯`, `LevelTransport.IsSectionTransport`: the transported sections $P,Q$ pull back correctly along any graded homomorphism realising a variable change, respectively a coefficient change).
--
--   **The moduli package $P_0$.** $P_0$ is a `LevelModuliPackageAbs` over $A_0$ for the datum `(rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum`: here the raw objects over an $A_0$-algebra $T$ are a Weierstrass curve with unit $\Delta$ together with a triple consisting of a family $h : \{p \mid M'\} \to T[X]$ of cyclic $p^{v_p(M')}$-kernel generators, a `LevelPData` which is a $\Gamma_1(\ell_g)$-point, and a `RawDrinfeldPair` which is of level (`RawDrinfeldPair.IsLevel 𝒢 q`: its curve is the given one and its two sections form a Drinfeld basis for the $q$-torsion divisor of the group law), subject to the link condition `IsGamma1Link W ℓg M' h D`, namely that if $\ell_g \mid M'$ then $h(\ell_g)$ divides `inLineMulPoly W ℓg (ℓg ^ (M'.factorization ℓg - 1)) D.xP`; points are variable-change classes of raw objects. Thus $P_0$ consists of an $A_0$-algebra $B_0$ and a class $P_0.\mathrm{univ}$ over it such that every class over every $A_0$-algebra $T$ is the image of $P_0.\mathrm{univ}$ under a unique $A_0$-algebra homomorphism $B_0 \to T$.
--
--   **The ring $R$ and the residue data.** $R$ is a Noetherian local $A_0$-algebra, complete for its maximal ideal, with an $A_0$-algebra homomorphism $\iota : B_0 \to R$; $k$ is a field of characteristic $q$ in which the images of $\ell_g$ and $M'$ are nonzero; $\mathrm{res}_R : R \to k$ is a surjective ring homomorphism with kernel the maximal ideal of $R$. Further, $W_0$ is a complete discrete valuation ring which is a domain with maximal ideal $(q)$, equipped with a surjection $\mathrm{res}_0 : W_0 \to k$ whose kernel is the maximal ideal, and $R$ is a $W_0$-algebra, $W_0$ an $A_0$-algebra, compatibly ($A_0 \to W_0 \to R$ a scalar tower), with $\mathrm{res}_R \circ (W_0 \to R) = \mathrm{res}_0$ (`hresR₀`). The hypothesis `hfac` is the pro-representability clause for $R$: for every Artinian local $W_0$- and $A_0$-algebra $T$ in the tower, with a surjection $\mathrm{res}_T : T \to k$ with kernel the maximal ideal and compatible with $\mathrm{res}_0$, every $A_0$-algebra homomorphism $\varphi : B_0 \to T$ satisfying $\mathrm{res}_T \circ \varphi = \mathrm{res}_R \circ \iota$ extends to a unique $W_0$-algebra homomorphism $\Phi : R \to T$ with $\mathrm{res}_T \circ \Phi = \mathrm{res}_R$ and $\Phi \circ \iota = \varphi$.
--
--   **The étale side over $W_0$.** The hypotheses `hℓ'`, `hM'`, `hL'` repeat the three transport hypotheses with $W_0$ in place of $A_0$, and `h𝒢r`, `h𝒢Or` assert that the restriction of scalars $\mathcal G.\mathrm{restrictScalars}\,W_0$ is chord–tangent and origin-normalised. $P^{\mathrm{et}}$ is a `LevelModuliPackageAbs` over $W_0$ for the level datum obtained from `(gamma0PowComponent W₀ M' hM').prod ((gamma1Component W₀ ℓg hℓ').prod LevelComponent.trivial)` by restricting to the link condition `IsGamma1Link W ℓg M' x.1 x.2.1`, made rigid; $x^{\mathrm{et}}$ is a raw object of this component over $P^{\mathrm{et}}.B_0$, and `hxet` asserts that its class equals $P^{\mathrm{et}}.\mathrm{univ}$.
--
--   **The $q$-torsion section.** $CQ$ is a commutative ring which is both a $P^{\mathrm{et}}.B_0$-algebra and a $W_0$-algebra in a scalar tower, and $Qu$ is a section of the projective model `projModelStrCR xet.curve` over $\mathrm{Spec}$ of the structure map $P^{\mathrm{et}}.B_0 \to CQ$; `hQu` says that $q \cdot Qu$ is the identity section for the group law $(\mathcal G.\mathrm{restrictScalars}\,W_0)$ attached to $x^{\mathrm{et}}.\mathrm{curve}$ and its unit discriminant. The hypothesis `hrep` states that $CQ$ together with $Qu$ represents the $q$-torsion: for every $P^{\mathrm{et}}.B_0$-algebra $T$ and every section $Q$ over it, $q \cdot Q$ is the identity section if and only if there is a unique $P^{\mathrm{et}}.B_0$-algebra homomorphism $\chi : CQ \to T$ such that `Spec.map` of $\chi$ followed by $Qu$ equals $Q$.
--
--   **The ring $S$.** $S$ is a Noetherian local $W_0$-algebra, complete for its maximal ideal, with a $W_0$-algebra homomorphism $\iota_S : CQ \to S$ and a surjection $\mathrm{res}_S : S \to k$ with kernel the maximal ideal and compatible with $\mathrm{res}_0$; `hfacS` is the corresponding pro-representability clause: every $W_0$-algebra homomorphism from $CQ$ to an Artinian local $W_0$-algebra $T$ with residue identification as above, agreeing with $\mathrm{res}_S \circ \iota_S$ after reduction, extends to a unique $W_0$-algebra homomorphism $S \to T$ compatible with the reductions and with $\iota_S$.
--
--   **The formal group and the polynomial $g$.** $F_S$ is a `FormalGroup S` whose underlying two-variable power series is the formal group law `formalGroupLawFixed` of $x^{\mathrm{et}}.\mathrm{curve}$ base-changed along $\iota_S \circ (P^{\mathrm{et}}.B_0 \to CQ)$. Moreover $g \in S[X]$ is monic of degree $q-1$, all its coefficients in degrees $< q-1$ lie in the maximal ideal of $S$, its constant coefficient is $q$ times a unit, $v$ is a unit power series over $S$, and `hfacq` asserts the factorisation of the $q$-th iterate series $F_S.\mathrm{nthSeries}\,q = X \cdot g \cdot v$ in $S\llbracket X\rrbracket$. Finally `hdom` asserts that `AdjoinRoot g` $= S[X]/(g)$ is a domain, and `hqS` that $q \neq 0$ in $S$.
--
--   **The distinguished $k$-point.** The field $k$ is an $A_0$-, $W_0$- and $P^{\mathrm{et}}.B_0$-algebra with $A_0 \to W_0 \to k$ a tower and $W_0 \to k$ equal to $\mathrm{res}_0$ (`hk₀`); $\rho : B_0 \to k$ is an $A_0$-algebra homomorphism with $\rho = \mathrm{res}_R \circ \iota$ (`hρ`); $\psi^{\mathrm{et}} : P^{\mathrm{et}}.B_0 \to k$ is a $W_0$-algebra homomorphism with $\psi^{\mathrm{et}} = \mathrm{res}_S \circ \iota_S \circ (P^{\mathrm{et}}.B_0 \to CQ)$ (`hψet`) and equal to the structure map $P^{\mathrm{et}}.B_0 \to k$ (`hψalg`); the discriminant of $x^{\mathrm{et}}.\mathrm{curve}$ pushed forward along $\psi^{\mathrm{et}}$ is a unit (`hΔk`); and $Q_k$ is a section of the resulting curve over $k$. The hypothesis `hQk_pin` pins $Q_k$ down: there exist a graded ring homomorphism $\varphi$ from `projModelGradingCR xet.curve` to the grading of the base-changed curve, and a containment $h\varphi$ of irrelevant ideals, such that $\varphi$ is a coefficient homomorphism for $\psi^{\mathrm{et}}$ (`IsCoefficientHom`) and $Q_k$ followed by `Proj.map φ hφ` equals `Spec.map` of $\mathrm{res}_S \circ \iota_S$ followed by $Qu$. The hypothesis `hQk` says $Q_k$ is not the identity section of $\mathcal G$ over $k$.
--
--   **Level conditions over $k$ and matching of the two universal points.** The reductions along $\psi^{\mathrm{et}}$ of the $\Gamma_0$-data satisfy `IsGamma0PowAt` at each prime power $p^{v_p(M')}$ with $p \mid M'$ (`hhk`), the reduced `LevelPData` is a $\Gamma_1(\ell_g)$-point (`hDk`), the link condition holds (`hLk`), and the pair consisting of the reduced curve, the identity section and $Q_k$ is of Drinfeld level $q$ (`hyk`). Finally `hρyk` asserts that the image of $P_0.\mathrm{univ}$ under $\rho$ in the point set of the datum `rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯` over $k$ is the class of the explicit raw object built from the reduced curve, its unit discriminant, the reduced $\Gamma_0(M')$-family, the reduced `LevelPData`, the Drinfeld pair (reduced curve, identity section, $Q_k$), and the proofs `hhk`, `hDk`, `hyk`, `hLk`.
--
--   **Conclusion.** Under these hypotheses the type of $W_0$-algebra isomorphisms $R \simeq S[X]/(g)$, that is `R ≃ₐ[W₀] AdjoinRoot g`, is nonempty.
--
--   This identifies the complete local ring $R$ of the moduli problem with $\Gamma_0(M') \cap \Gamma_1(\ell_g)$-structure together with Drinfeld $\Gamma(q)$-structure, at an ordinary point over $k$, with the root extension $S[X]/(g)$ of the corresponding ring on the étale side, where $g$ is the degree $q-1$ Eisenstein-type factor of the $q$-th iterate series of the formal group. It is used in the deduction of the power-series description of such local rings, via the statement [`ModularCurve.LevelModuliPackageAbs.exists_algEquiv_adjoinRoot_powerSeries_of_nthSeries_eq_mul_X_pow_of_eq_one_of_ne_one_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_algEquiv_adjoinRoot_powerSeries_of_nthSeries_eq_mul_X_pow_of_eq_one_of_ne_one_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_nonempty_algEquiv_adjoinRoot_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_rigidDataH1Pow.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
  AlgebraicGeometry CategoryTheory NeronModelInfra Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.nonempty_algEquiv_adjoinRoot_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_rigidDataH1Pow
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
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
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
        ∀ φ : P₀.B₀ →ₐ[A₀] T, (∀ b : P₀.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : P₀.B₀, Φ (ι b) = φ b)

    (hℓ' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))

    (h𝒢r : (𝒢.restrictScalars W₀).IsChordTangent) (h𝒢Or : (𝒢.restrictScalars W₀).IsOriginIdentity)
    (Pet : LevelModuliPackageAbs W₀
      ((((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.gamma1Component W₀ ℓg hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL' _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum)
    (xet : ((((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.gamma1Component W₀ ℓg hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL' _ W C _ _ _ _ (hx hmem))).toRigid).Raw Pet.B₀)
    (hxet : (Quot.mk _ xet :
      ((((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.gamma1Component W₀ ℓg hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL' _ W C _ _ _ _ (hx hmem))).toRigid).Pt Pet.B₀) =
        Pet.univ)
    (CQ : Type) [CommRing CQ] [Algebra Pet.B₀ CQ] [Algebra W₀ CQ] [IsScalarTower W₀ Pet.B₀ CQ]
    (Qu : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ CQ))) (projModelStrCR xet.curve))
    (hQu : ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q Qu =
      ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _)
    (hrep : ∀ (T : Type) [CommRing T] [Algebra Pet.B₀ T]
        (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ T))) (projModelStrCR xet.curve)),
        ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q Q =
            ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _ ↔
          ∃! χ : CQ →ₐ[Pet.B₀] T, Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Qu.1 = Q.1)

    (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    [Algebra W₀ S] (ιS : CQ →ₐ[W₀] S)
    (resS : S →+* k) (hresS : Function.Surjective resS) (hkerS : RingHom.ker resS = maximalIdeal S)
    (hresS₀ : ∀ w : W₀, resS (algebraMap W₀ S w) = res₀ w)
    (hfacS : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : CQ →ₐ[W₀] T, (∀ c : CQ, resT (φ c) = resS (ιS c)) →
          ∃! Φ : S →ₐ[W₀] T, (∀ s : S, resT (Φ s) = resS s) ∧ ∀ c : CQ, Φ (ιS c) = φ c)

    (FS : FormalGroup S)
    (hFS : FS.toPowerSeries = (xet.curve.map ((ιS : CQ →+* S).comp (algebraMap Pet.B₀ CQ))).formalGroupLawFixed)
    (g : S[X]) (v : PowerSeries S) (hgm : g.Monic) (hgdeg : g.natDegree = q - 1)
    (hgcoeff : ∀ i < q - 1, g.coeff i ∈ maximalIdeal S) (hg0 : ∃ w : S, IsUnit w ∧ g.coeff 0 = (q : S) * w)
    (hv : IsUnit v)
    (hfacq : FS.nthSeries q = PowerSeries.X * (↑g : PowerSeries S) * v)

    (hdom : IsDomain (AdjoinRoot g)) (hqS : (q : S) ≠ 0)

    [Algebra A₀ k] [Algebra W₀ k] [IsScalarTower A₀ W₀ k] [Algebra Pet.B₀ k]
    (hk₀ : ∀ w : W₀, algebraMap W₀ k w = res₀ w)
    (ρ : P₀.B₀ →ₐ[A₀] k) (hρ : ∀ b : P₀.B₀, ρ b = resR (ι b))
    (ψet : Pet.B₀ →ₐ[W₀] k) (hψet : ∀ b : Pet.B₀, ψet b = resS (ιS (algebraMap Pet.B₀ CQ b)))
    (hψalg : ∀ b : Pet.B₀, algebraMap Pet.B₀ k b = ψet b)
    (hΔk : IsUnit (xet.curve.map ψet.toRingHom).Δ)
    (Qk : Section (xet.curve.map ψet.toRingHom))
    (hQk_pin : ∃ (φ : projModelGradingCR xet.curve →+*ᵍ projModelGradingCR (xet.curve.map ψet.toRingHom))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (xet.curve.map ψet.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR xet.curve)).map φ),
        IsCoefficientHom xet.curve ψet.toRingHom φ ∧
          Qk.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1)
    (hQk : Qk ≠ (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))))

    (hhk : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt (xet.curve.map ψet.toRingHom) (p : ℕ) (M'.factorization (p : ℕ))
      ((xet.level.1 p).map ψet.toRingHom))
    (hDk : ModularCurve.IsGamma1Point (xet.curve.map ψet.toRingHom) ℓg (xet.level.2.1.map ψet.toRingHom))
    (hLk : ModularCurve.IsGamma1Link (xet.curve.map ψet.toRingHom) ℓg M'
      (fun p => (xet.level.1 p).map ψet.toRingHom) (xet.level.2.1.map ψet.toRingHom))
    (hyk : RawDrinfeldPair.IsLevel 𝒢 q (xet.curve.map ψet.toRingHom)
      ⟨xet.curve.map ψet.toRingHom, (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩)
    (hρyk : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map ρ P₀.univ =
      (Quot.mk _ (⟨xet.curve.map ψet.toRingHom, hΔk,
          ⟨fun p => (xet.level.1 p).map ψet.toRingHom, xet.level.2.1.map ψet.toRingHom,
            ⟨xet.curve.map ψet.toRingHom, (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩⟩,
          ⟨⟨hhk, hDk, hyk⟩, hLk⟩⟩ : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw k) :
        (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt k)) :
    Nonempty (R ≃ₐ[W₀] AdjoinRoot g) := by sorry
