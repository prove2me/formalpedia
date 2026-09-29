-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_equiv_isDrinfeldBasisOver_natural_of_factorsThrough_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algHom_equiv_isDrinfeldBasisOver_natural_of_factorsThrough_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/d0769f18-1fcc-5a85-9b62-092c2e9d5062
-- title:
--   Natural normal form for W₀-algebra maps out of R
-- statement:
--   Throughout, $q$ is a prime, $\ell_g$ and $M'$ are natural numbers with $\ell_g$ prime, $\ell_g \equiv 11 \pmod{12}$ and $M' \neq 0$, and $A_0$ is a commutative ring.
--
--   **Transport hypotheses over $A_0$.** The hypothesis `hℓ` states that for every $A_0$-algebra $T$, every Weierstrass curve $W/T$, every variable change $C$ and every [`ModularCurve.LevelPData T`](def/ModularCurve_KatzLevelP.html#L43) $D$ (a quadruple $x_P,y_P,x_Q,y_Q \in T$), the predicate [`ModularCurve.IsGamma1Point W ℓg D`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) — namely that $(x_P,y_P)$ satisfies the affine Weierstrass equation of $W$, that $(W.\mathrm{pre}\Psi\,\ell_g)(x_P)=0$, and that $x_Q=x_P$, $y_Q=y_P$ — is carried by $C$ to `IsGamma1Point (C • W) ℓg (D.variableChange C)`. The hypothesis `hM` states that [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) (for $p^k=2$ the condition `IsTwoKernel`: $\deg h \le 1$, $h$ has coefficient $1$ in degree $1$ and $h \mid W.\Psi_2^{\,2}$; otherwise `IsCyclicGenKernel p k h`: $\deg h \le \varphi(p^k)/2$, the coefficient of $h$ in degree $\varphi(p^k)/2$ is $1$, $h\cdot W.\mathrm{pre}\Psi(p^{k-1}) \mid W.\mathrm{pre}\Psi(p^k)$, and $h$ divides the relevant multiplication numerators) is carried to `IsGamma0PowAt (C • W) p k` of `kernelVariableChangeDeg C (gamma0PowDeg p k) h`, the twisted composite $C(u^{-1})^{2d}\,h(C(u)^2X + C(r))$. The hypothesis `hL` states that a divisibility $h \mid \mathrm{inLineMulPoly}\,W\,\ell_g\,n\,x$ is carried to $\mathrm{kernelVariableChangeDeg}\,C\,d\,h \mid \mathrm{inLineMulPoly}\,(C\bullet W)\,\ell_g\,n\,(u^{-2}(x-r))$.
--
--   **Group laws and the full-level package.** $\mathcal G$ is a `GroupLaws A₀`, i.e. a relative group law on the Proj model `projModelStrCR W` for every projective Weierstrass curve $W$ over an $A_0$-algebra with unit discriminant; `h𝒢` asserts that each of these admits a points-evaluation (chord–tangent) presentation and `h𝒢O` that the unit section is pinned by an origin-chart homomorphism killing $x/y$ and $z/y$. $\mathcal T$ is a `LevelTransport A₀ 𝒢 q` and `h𝒯` asserts it is a section transport: its variable-change and base-change operations agree with the given sections $P,Q$ after composition with the corresponding `Proj.map` of a variable-change, resp. coefficient, graded homomorphism. $P_0$ is a fine moduli package `LevelModuliPackageAbs A₀` for the moduli datum attached to `rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯`: the level component is the product of the $\Gamma_0$-kernel component for $M'$, the $\Gamma_1(\ell_g)$-point component and the Drinfeld $\Gamma(q)$-level component built from $\mathcal G,\mathcal T$, restricted along the link condition `IsGamma1Link W ℓg M'`; thus $P_0$ consists of an $A_0$-algebra $B_0$ and a point `P₀.univ` such that every point of the functor over any $A_0$-algebra is the image of `P₀.univ` under a unique $A_0$-algebra map.
--
--   **The deformation ring $R$ and its hull property.** $R$ is a noetherian local ring, adically complete for its maximal ideal and an $A_0$-algebra, with an $A_0$-algebra map $\iota : B_0 \to R$; $k$ is a field of characteristic $q$ in which $\ell_g$ and $M'$ are nonzero (`hℓk`, `hM'k`); $\mathrm{res}_R : R \to k$ is surjective with kernel the maximal ideal (`hresR`, `hkerR`). $W_0$ is a complete discrete valuation domain with maximal ideal $(q)$ (`hW₀`) and surjective $\mathrm{res}_0 : W_0 \to k$ with kernel the maximal ideal (`hres₀`, `hker₀`); $R$ is a $W_0$-algebra compatibly with its $A_0$-structure, and `hresR₀` says $\mathrm{res}_R \circ \mathrm{algebraMap}\,W_0\,R = \mathrm{res}_0$. The hypothesis `hfac` is the factorisation (hull) property: for every Artinian local $W_0$- and $A_0$-algebra $T$ with compatible towers and every surjective $\mathrm{res}_T : T \to k$ with kernel the maximal ideal and lying over $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi : B_0 \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R \circ \iota$, there is a unique $W_0$-algebra map $\Phi : R \to T$ with $\mathrm{res}_T \circ \Phi = \mathrm{res}_R$ and $\Phi \circ \iota = \varphi$.
--
--   **Transport over $W_0$ and the level-away-from-$q$ package.** The hypotheses `hℓ'`, `hM'`, `hL'` repeat `hℓ`, `hM`, `hL` for $W_0$-algebras, and `h𝒢r`, `h𝒢Or` assert that `𝒢.restrictScalars W₀` is chord–tangent and origin-pinned. `Pet` is a fine moduli package over $W_0$ for the datum whose level component is the product of the $\Gamma_0$-kernel component for $M'$, the $\Gamma_1(\ell_g)$-point component and the trivial component, restricted along `IsGamma1Link W ℓg M'` (so no $q$-level structure enters). `xet` is a raw object of that component over `Pet.B₀`: a Weierstrass curve `xet.curve` with unit discriminant, level data consisting of a family of polynomials indexed by the prime factors of $M'$, a `LevelPData` and the trivial datum, together with the corresponding level conditions; `hxet` says that the class of `xet` in the quotient by the variable-change relation is `Pet.univ`.
--
--   **The $q$-torsion algebra and the ring $S$.** $C_Q$ is a commutative ring, an algebra over `Pet.B₀` and over $W_0$ with compatible towers, and $Q_u$ is a section of `projModelStrCR xet.curve` over $\operatorname{Spec}$ of $\mathrm{algebraMap}\,\mathrm{Pet.B₀}\,C_Q$; `hQu` says $q\cdot Q_u$ equals the unit section for the group law $(\mathcal G$ restricted to $W_0)$ at `Pet.B₀`, `xet.curve`, `xet.isUnit_Δ`, and `hrep` says $C_Q$ represents the $q$-torsion: for every `Pet.B₀`-algebra $T$ and every section $Q$ over $T$, $q\cdot Q$ is the unit section if and only if there is a unique `Pet.B₀`-algebra map $\chi : C_Q \to T$ with $\operatorname{Spec}\chi$ followed by $Q_u$ equal to $Q$. $S$ is a noetherian local ring, adically complete for its maximal ideal and a $W_0$-algebra, with $\iota_S : C_Q \to S$ a $W_0$-algebra map and a surjection $\mathrm{res}_S : S \to k$ whose kernel is the maximal ideal and which lies over $\mathrm{res}_0$ (`hresS`, `hkerS`, `hresS₀`); `hfacS` is the analogous factorisation property of $(S,\iota_S,\mathrm{res}_S)$ over $C_Q$ for Artinian local $W_0$-algebras.
--
--   **Formal-group factorisation.** $F_S$ is a formal group over $S$ whose power series is the fixed formal group law of `xet.curve` base-changed along $\iota_S \circ \mathrm{algebraMap}\,\mathrm{Pet.B₀}\,C_Q$ (`hFS`); $g \in S[X]$ is monic of degree $q-1$ with all coefficients of index $<q-1$ in the maximal ideal and constant coefficient $q$ times a unit, $v$ is a unit power series, and `hfacq` gives $F_S.\mathrm{nthSeries}\,q = X \cdot g \cdot v$.
--
--   **Residual data.** $k$ is made an algebra over $A_0$, over $W_0$ (with $\mathrm{algebraMap}\,W_0\,k = \mathrm{res}_0$, `hk₀`) and over `Pet.B₀`; $\rho : B_0 \to k$ is an $A_0$-algebra map with $\rho = \mathrm{res}_R \circ \iota$ (`hρ`); $\psi_{et} : \mathrm{Pet.B₀} \to k$ is a $W_0$-algebra map with $\psi_{et}(b) = \mathrm{res}_S(\iota_S(\mathrm{algebraMap}\,b))$ (`hψet`) and equal to the structure map $\mathrm{algebraMap}\,\mathrm{Pet.B₀}\,k$ (`hψalg`); `hΔk` says the discriminant of `xet.curve` base-changed along $\psi_{et}$ is a unit; $Q_k$ is a section of that curve over $k$; `hQk_pin` asserts the existence of a graded homomorphism $\phi$ from `projModelGradingCR xet.curve` to the grading of the base-changed curve, with the irrelevant-ideal condition, which is a coefficient homomorphism for $\psi_{et}$ and satisfies: $Q_k$ followed by `Proj.map φ` equals $\operatorname{Spec}(\mathrm{res}_S \circ \iota_S)$ followed by $Q_u$; and `hQk` says $Q_k$ is not the unit section. Further, `hhk`, `hDk`, `hLk` assert the $\Gamma_0(p^{v_p(M')})$-kernel conditions for each prime factor $p$ of $M'$, the $\Gamma_1(\ell_g)$-point condition and the link condition for the reduced level data; `hyk` asserts that the raw Drinfeld pair consisting of the reduced curve, the unit section and $Q_k$ has level in the sense of `RawDrinfeldPair.IsLevel 𝒢 q`, i.e. its curve is the given one and, for a unit discriminant, the basis divisor of the pair equals the $q$-torsion ideal; and `hρyk` states that $\rho$ carries `P₀.univ` to the class over $k$ of the raw object assembled from the reduced curve, the reduced level data and that Drinfeld pair.
--
--   **Conclusion.** There exists a family $\alpha$ which assigns, to every Artinian local $W_0$-algebra $T$ and every ring homomorphism $\mathrm{res}_T : T \to k$ which is surjective, has kernel the maximal ideal of $T$, and satisfies $\mathrm{res}_T \circ \mathrm{algebraMap}\,W_0\,T = \mathrm{res}_0$, an equivalence between $W_0$-algebra maps $R \to T$ and the set of triples $d = (d_1,(d_{2,1},d_{2,2}))$, where $d_1 : \mathrm{Pet.B₀} \to_{W_0} T$ and $d_{2,1}, d_{2,2}$ are morphisms $\operatorname{Spec} T \to$ `projModelCR xet.curve`, subject to the following four conditions:
--
--   (i) $\mathrm{res}_T(d_1 b) = \psi_{et}(b)$ for all $b \in \mathrm{Pet.B₀}$;
--
--   (ii) there are proofs $h_P$ that $d_{2,1}$ followed by `projModelStrCR xet.curve` equals $\operatorname{Spec}(d_1)$, and $h_Q$ the same for $d_{2,2}$, such that the pair $(\langle d_{2,1},h_P\rangle, \langle d_{2,2},h_Q\rangle)$ satisfies `IsDrinfeldBasisOver q` for the group law $(\mathcal G$ restricted to $W_0)$ at `Pet.B₀`, `xet.curve`, `xet.isUnit_Δ` over the base morphism $\operatorname{Spec}(d_1)$ — that is, the basis divisor sheaf data of the pair coincides with the $q$-torsion ideal sheaf data — and moreover $q\cdot\langle d_{2,2},h_Q\rangle$ is the unit section;
--
--   (iii) $\operatorname{Spec}(\mathrm{res}_T)$ followed by $d_{2,1}$ equals the underlying morphism of the unit section of that group law over $\operatorname{Spec}(\psi_{et})$;
--
--   (iv) $\operatorname{Spec}(\mathrm{res}_T)$ followed by $d_{2,2}$ equals $\operatorname{Spec}(\mathrm{res}_S \circ \iota_S)$ followed by $Q_u$.
--
--   The family $\alpha$ is natural in the following sense: for any two Artinian local $W_0$-algebras $T$, $T'$ with residue maps $\mathrm{res}_T$, $\mathrm{res}_{T'}$ as above, any $W_0$-algebra map $f : T \to T'$ with $\mathrm{res}_{T'} \circ f = \mathrm{res}_T$, and any $\varphi : R \to_{W_0} T$, the underlying triple of $\alpha_{T'}(f \circ \varphi)$ equals $(f \circ (\alpha_T \varphi)_1,\ (\operatorname{Spec}(f)$ followed by $(\alpha_T\varphi)_{2,1},\ \operatorname{Spec}(f)$ followed by $(\alpha_T\varphi)_{2,2}))$.
--
--   This is the normal-form description of the functor of points of the complete local ring $R$ at level $\Gamma_0(M') \cap \Gamma_1(\ell_g)$ together with Drinfeld $\Gamma(q)$-structure: a $W_0$-algebra map $R \to T$ is the same as an algebra map on the level-away-from-$q$ parameter ring together with a relative Drinfeld $q$-basis whose first member reduces to the origin and whose second member reduces to the universal $q$-torsion point, compatibly with change of the Artinian test ring. It is used in the identification of $R$ with the relevant ring of functions on the ordinary locus, via the formal-group factorisation of $[q]$ recorded in the hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_equiv_isDrinfeldBasisOver_natural_of_factorsThrough_rigidDataH1Pow.lean

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
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
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

theorem ModularCurve.LevelModuliPackageAbs.exists_algHom_equiv_isDrinfeldBasisOver_natural_of_factorsThrough_rigidDataH1Pow
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
    ∃ α : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w),
          (R →ₐ[W₀] T) ≃
          {d : (Pet.B₀ →ₐ[W₀] T) ×
              ((base (T := T) ⟶ projModelCR xet.curve) × (base (T := T) ⟶ projModelCR xet.curve)) //
            (∀ b : Pet.B₀, resT (d.1 b) = ψet b) ∧
            (∃ (hP : d.2.1 ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom d.1.toRingHom))
               (hQ : d.2.2 ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom d.1.toRingHom)),
               ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                 (Spec.map (CommRingCat.ofHom d.1.toRingHom)) ⟨d.2.1, hP⟩ ⟨d.2.2, hQ⟩ ∧
               ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q ⟨d.2.2, hQ⟩ =
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _) ∧
            Spec.map (CommRingCat.ofHom resT) ≫ d.2.1 =
              (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1 ∧
            Spec.map (CommRingCat.ofHom resT) ≫ d.2.2 =
              Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1},
      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
        (T' : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [Algebra W₀ T']
        (resT' : T' →+* k) (hT'₁ : Function.Surjective resT') (hT'₂ : RingHom.ker resT' = maximalIdeal T')
        (hT'₃ : ∀ w : W₀, resT' (algebraMap W₀ T' w) = res₀ w)
        (f : T →ₐ[W₀] T') (_ : ∀ t : T, resT' (f t) = resT t) (φ : R →ₐ[W₀] T),
        ((α T' resT' hT'₁ hT'₂ hT'₃ (f.comp φ)).1 :
            (Pet.B₀ →ₐ[W₀] T') × ((base (T := T') ⟶ projModelCR xet.curve) × (base (T := T') ⟶ projModelCR xet.curve))) =
          (f.comp (α T resT hT₁ hT₂ hT₃ φ).1.1,
            (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (α T resT hT₁ hT₂ hT₃ φ).1.2.1,
             Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (α T resT hT₁ hT₂ hT₃ φ).1.2.2)) := by sorry
