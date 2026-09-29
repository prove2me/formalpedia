-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_section_equiv_isDrinfeldBasisOver_isDrinfeldBasis_of_isCoefficientHom_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_section_equiv_isDrinfeldBasisOver_isDrinfeldBasis_of_isCoefficientHom_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/4ec9a8f8-97b4-5269-9e1a-b85ca4a89355
-- title:
--   Transport of q-torsion sections and Drinfeld bases at level H₁
-- statement:
--   Fix a prime $q$, natural numbers $\ell_g$ and $M'$ with $\ell_g$ prime, $\ell_g \equiv 11 \pmod{12}$ and $M' \neq 0$, and a commutative ring $A_0$.
--
--   **Transport hypotheses over $A_0$.** Three hypotheses record that the level structures are stable under Weierstrass variable changes over arbitrary commutative $A_0$-algebras $T$: `hℓ` states that if [`ModularCurve.IsGamma1Point W ℓg D`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) holds for a Weierstrass curve $W$ over $T$ and a `LevelPData` $D=(x_P,y_P,x_Q,y_Q)$ (i.e. $(x_P,y_P)$ satisfies the affine equation of $W$, $(W.\mathrm{pre}\Psi\,\ell_g)(x_P)=0$, $x_Q=x_P$ and $y_Q=y_P$), then the same holds for $C \bullet W$ and the transformed datum `D.variableChange C`; `hM` states that [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) is carried to [`ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h)`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) (here `IsGamma0PowAt` is `IsTwoKernel` when $p^k=2$ and `IsCyclicGenKernel p k` otherwise); `hL` states that a divisor $h$ of [`ModularCurve.inLineMulPoly W ℓg n x`](def/ModularCurve_WeierstrassH1Pow.html#L18) is carried, as [`ModularCurve.kernelVariableChangeDeg C d h`](def/ModularCurve_WeierstrassLevelComponents.html#L104), to a divisor of [`ModularCurve.inLineMulPoly (C • W) ℓg n (u^{-2}(x-r))`](def/ModularCurve_WeierstrassH1Pow.html#L18) for the data $C=(u,r,s,t)$.
--
--   **Group-law data over $A_0$.** $\mathcal G$ is a `GroupLaws A₀`, i.e. a family assigning to every $A_0$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with unit discriminant a relative group law on `projModelStrCR W`; `h𝒢` asserts that each member admits a points-evaluation (chord–tangent) description and `h𝒢O` that for each member the unit section is the origin section in the origin chart, with $x/y$ and $z/y$ mapping to $0$. $\mathcal T$ is a `LevelTransport A₀ 𝒢 q` and `h𝒯` asserts `IsSectionTransport`, the two compatibility clauses stating that the variable-change action and the base-change map of $\mathcal T$ are computed on the underlying sections by composition with the corresponding `Proj.map` of a variable-change, resp. coefficient, homomorphism.
--
--   **The moduli package at level $H_1$.** $P_0$ is a `LevelModuliPackageAbs` over $A_0$ for the moduli datum of `rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯`: a ring $P_0.B_0$, a point `P₀.univ` of the functor at $P_0.B_0$, and the property that for every $A_0$-algebra $T$ and every point $x$ at $T$ there is a unique $A_0$-algebra map $P_0.B_0 \to T$ carrying `univ` to $x$. Here the underlying level component is the product of the $\Gamma_0$-component `gamma0PowComponent A₀ M' hM` (tuples of polynomials indexed by the prime factors $p$ of $M'$, with `IsGamma0PowAt` at exponent $v_p(M')$), the $\Gamma_1$-component `gamma1Component A₀ ℓg hℓ` (a `LevelPData` satisfying `IsGamma1Point`) and the Drinfeld component `levelComponent A₀ 𝒢 q 𝒯`, restricted by the link condition `IsGamma1Link W ℓg M' x.1 x.2.1` (if $\ell_g \mid M'$, the $\ell_g$-th kernel polynomial divides $\mathrm{inLineMulPoly}\,W\,\ell_g\,(\ell_g^{v_{\ell_g}(M') - 1})\,x_P$), the points at $T$ being variable-change classes of such raw data with unit discriminant.
--
--   **The deformation ring $R$ and the coefficient ring $W_0$.** $R$ is a noetherian local $A_0$-algebra, complete for the adic topology of its maximal ideal, equipped with $\iota : P_0.B_0 \to_{A_0} R$; $k$ is a field of characteristic $q$ in which $\ell_g$ and $M'$ are nonzero; $\mathrm{res}_R : R \to k$ is surjective with kernel the maximal ideal. $W_0$ is a complete discrete valuation domain with maximal ideal $(q)$, with a surjection $\mathrm{res}_0 : W_0 \to k$ whose kernel is its maximal ideal; $R$ is a $W_0$-algebra, $W_0$ an $A_0$-algebra, the scalar towers agree, and `hresR₀` says $\mathrm{res}_R$ restricted along $W_0 \to R$ is $\mathrm{res}_0$. The hypothesis `hfac` is the universal property of $(R,\iota)$: for every artinian local ring $T'$ that is simultaneously a $W_0$- and $A_0$-algebra compatibly, every surjection $\mathrm{res}_{T'} : T' \to k$ with kernel the maximal ideal and restricting to $\mathrm{res}_0$ on $W_0$, and every $A_0$-algebra map $\varphi : P_0.B_0 \to T'$ with $\mathrm{res}_{T'} \circ \varphi = \mathrm{res}_R \circ \iota$, there is a unique $W_0$-algebra map $\Phi : R \to T'$ with $\mathrm{res}_{T'} \circ \Phi = \mathrm{res}_R$ and $\Phi \circ \iota = \varphi$.
--
--   **Transport over $W_0$.** `hℓ'`, `hM'`, `hL'` are the three transport hypotheses above stated for $W_0$-algebras, and `h𝒢r`, `h𝒢Or` assert that `𝒢.restrictScalars W₀` is chord–tangent and origin-identity.
--
--   **The étale-level package.** $P_{\mathrm{et}}$ is a `LevelModuliPackageAbs` over $W_0$ for the rigid data obtained from the level component $(\Gamma_0(M')\text{-component}) \times ((\Gamma_1(\ell_g)\text{-component}) \times \text{trivial})$ over $W_0$, restricted by the same link condition; thus the Drinfeld slot is the trivial component. $x_{\mathrm{et}}$ is a raw point of this component over $P_{\mathrm{et}}.B_0$: a Weierstrass curve `xet.curve` with unit discriminant, a family of kernel polynomials `xet.level.1`, a `LevelPData` `xet.level.2.1`, a trivial third entry, together with the level and link conditions; `hxet` says that its class in the point functor at $P_{\mathrm{et}}.B_0$ is `Pet.univ`.
--
--   **The $q$-torsion representing ring $CQ$.** $CQ$ is a commutative ring which is both a $P_{\mathrm{et}}.B_0$-algebra and a $W_0$-algebra with compatible towers; $Q_u$ is a morphism $\mathrm{Spec}\,CQ \to$ `projModelCR xet.curve` over `Spec.map (algebraMap Pet.B₀ CQ)`; `hQu` says that $q \cdot Q_u$ is the unit section for the group law `(𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ` (the iterated `nsmul`); and `hrep` is the universal property: for every $P_{\mathrm{et}}.B_0$-algebra $T'$ and every point $Q$ of the Proj model over the structure morphism, $q \cdot Q$ is the unit section if and only if there is a unique $P_{\mathrm{et}}.B_0$-algebra map $\chi : CQ \to T'$ such that $\mathrm{Spec}\,\chi$ followed by $Q_u$ equals $Q$.
--
--   **The ring $S$ and the $q$-series factorisation.** $S$ is a noetherian local $W_0$-algebra, complete for its maximal-adic topology, with $\iota_S : CQ \to_{W_0} S$, a surjection $\mathrm{res}_S : S \to k$ with kernel the maximal ideal restricting to $\mathrm{res}_0$ on $W_0$, and the universal property `hfacS` of $(S,\iota_S)$ with respect to artinian local $W_0$-algebras, exactly parallel to `hfac`. $F_S$ is a formal group over $S$ whose power series is the formal group law `formalGroupLawFixed` of the base change of `xet.curve` along $\iota_S \circ (P_{\mathrm{et}}.B_0 \to CQ)$. Finally $g \in S[X]$ is monic of degree $q-1$ with all coefficients of index $< q-1$ in the maximal ideal and constant coefficient $q$ times a unit, $v$ is a unit power series, and `hfacq` states $F_S.\mathrm{nthSeries}\,q = X \cdot g \cdot v$.
--
--   **The residual situation.** $k$ is an $A_0$-, $W_0$- and $P_{\mathrm{et}}.B_0$-algebra with compatible towers, the $W_0$-structure being $\mathrm{res}_0$ (`hk₀`); $\rho : P_0.B_0 \to_{A_0} k$ equals $\mathrm{res}_R \circ \iota$; $\psi_{\mathrm{et}} : P_{\mathrm{et}}.B_0 \to_{W_0} k$ equals $\mathrm{res}_S \circ \iota_S$ on the image of $P_{\mathrm{et}}.B_0$ in $CQ$ and induces the given $P_{\mathrm{et}}.B_0$-algebra structure on $k$; the base change of `xet.curve` along $\psi_{\mathrm{et}}$ has unit discriminant ($h\Delta k$); $Q_k$ is a section of that curve over $k$; `hQk_pin` asserts the existence of a graded homomorphism $\varphi$ of the Proj gradings with the irrelevant-ideal condition, satisfying `IsCoefficientHom xet.curve ψet.toRingHom φ` (i.e. $\varphi$ sends the class of a constant $a$ to the class of the constant $\psi_{\mathrm{et}}(a)$ and fixes the classes of the three coordinates), such that $Q_k$ followed by `Proj.map φ` equals $\mathrm{Spec}(\mathrm{res}_S \circ \iota_S)$ followed by $Q_u$; `hQk` says $Q_k$ is not the unit section. Furthermore `hhk`, `hDk`, `hLk` assert the $\Gamma_0(M')$-, $\Gamma_1(\ell_g)$- and link conditions for the reductions of the level data along $\psi_{\mathrm{et}}$, and `hyk` asserts `RawDrinfeldPair.IsLevel 𝒢 q` for the triple consisting of the reduced curve, the unit section and $Q_k$, that is, that the pair (origin, $Q_k$) is a Drinfeld basis of level $q$ for the member law at $k$. Finally `hρyk` identifies the image of `P₀.univ` under $\rho$ with the class of the explicit raw datum over $k$ built from the reduced curve, the reduced level data and that Drinfeld pair.
--
--   **The test datum.** $T$ is an artinian local $W_0$-algebra with a surjection $\mathrm{res}_T : T \to k$ whose kernel is the maximal ideal and which restricts to $\mathrm{res}_0$ on $W_0$; $\psi : P_{\mathrm{et}}.B_0 \to_{W_0} T$ satisfies $\mathrm{res}_T \circ \psi = \psi_{\mathrm{et}}$; $Q_m : \mathrm{Spec}\,T \to$ `projModelCR xet.curve` lies over $\mathrm{Spec}\,\psi$ (`hQover`), is $q$-torsion for the law `(𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ` (`hQtors`), and reduces to the pinned point: $\mathrm{Spec}(\mathrm{res}_T)$ followed by $Q_m$ equals $\mathrm{Spec}(\mathrm{res}_S \circ \iota_S)$ followed by $Q_u$ (`hQred`).
--
--   **Conclusion.** Under these hypotheses there exists a section $Q$ of the base change `xet.curve.map ψ.toRingHom` over $T$ such that:
--
--   (i) $q \cdot Q$ is the unit section for the member law `(𝒢.restrictScalars W₀) T (xet.curve.map ψ.toRingHom)` at the transported unit discriminant;
--
--   (ii) for no ring homomorphism $\chi$ from the origin chart ring of `xet.curve.map ψ.toRingHom` to $T$ does `ReducesToOrigin Q χ (maximalIdeal T)` hold, that is, $Q$ does not reduce to the origin modulo the maximal ideal;
--
--   (iii) for every graded homomorphism $\varphi$ of the Proj gradings with the irrelevant-ideal condition satisfying `IsCoefficientHom xet.curve ψ.toRingHom φ`, the composite of $Q$ with `Proj.map φ` is $Q_m$;
--
--   (iv) there is a bijection $e$ between, on one side, the set of morphisms $P_m : \mathrm{Spec}\,T \to$ `projModelCR xet.curve` such that $P_m$ and $Q_m$ both lie over $\mathrm{Spec}\,\psi$ and the resulting pair is a relative Drinfeld basis of level $q$ over $\mathrm{Spec}\,\psi$ for the $P_{\mathrm{et}}.B_0$-law (`IsDrinfeldBasisOver`: equality of the basis divisor of the pair with the $q$-torsion ideal sheaf datum over that base), and such that $\mathrm{Spec}(\mathrm{res}_T)$ followed by $P_m$ is the unit section over $\mathrm{Spec}\,\psi_{\mathrm{et}}$, and, on the other side, the set of sections $P$ of `xet.curve.map ψ.toRingHom` which reduce to the origin modulo the maximal ideal of $T$ (for some chart homomorphism $\chi$) and for which $(P,Q)$ is a Drinfeld basis of level $q$ for the member law at $T$; and the bijection $e$ is compatible with the transfer along coefficient homomorphisms: for every such $P_m$, every graded homomorphism $\varphi$ with the irrelevant-ideal condition and `IsCoefficientHom xet.curve ψ.toRingHom φ`, the composite of the section $e(P_m)$ with `Proj.map φ` equals $P_m$.
--
--   This is the comparison, at the level structure $\Gamma_0(M') \cap \Gamma_1(\ell_g)$ together with a Drinfeld $\Gamma(q)$-structure, between $T$-points of the Proj model of the universal curve of the étale-level problem and Drinfeld bases of the base-changed curve: a $q$-torsion point $Q_m$ lifting the pinned residual point is realised by a section $Q$ that does not meet the origin, and the relative Drinfeld partners of $Q_m$ over $\mathrm{Spec}\,\psi$ correspond bijectively, compatibly with the Proj transfer, to the absolute Drinfeld partners of $Q$ which do reduce to the origin. It feeds the construction of the identification of the deformation-theoretic point set with the zero set attached to the factorisation of the $q$-series, used in the analysis of the moduli package at this level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_section_equiv_isDrinfeldBasisOver_isDrinfeldBasis_of_isCoefficientHom_rigidDataH1Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.exists_section_equiv_isDrinfeldBasisOver_isDrinfeldBasis_of_isCoefficientHom_rigidDataH1Pow
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
        (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt k))
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (ψ : Pet.B₀ →ₐ[W₀] T) (hψ₀ : ∀ b : Pet.B₀, resT (ψ b) = ψet b)
    (Qm : base (T := T) ⟶ projModelCR xet.curve)
    (hQover : Qm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom ψ.toRingHom))
    (hQtors : ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q ⟨Qm, hQover⟩ = ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _)
    (hQred : Spec.map (CommRingCat.ofHom resT) ≫ Qm = Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1) :
    ∃ Q : Section (xet.curve.map (ψ).toRingHom),
      ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).nsmul (𝟙 _) q Q =
        ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).one (𝟙 _) ∧
      (∀ χ : OriginChartRing (xet.curve.map ψ.toRingHom) →+* T, ¬ ReducesToOrigin Q χ (maximalIdeal T)) ∧
      (∀ (φ : projModelGradingCR xet.curve →+*ᵍ projModelGradingCR (xet.curve.map ψ.toRingHom))
          (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (xet.curve.map ψ.toRingHom)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR xet.curve)).map φ),
          IsCoefficientHom xet.curve ψ.toRingHom φ → Q.1 ≫ Proj.map φ hφ = Qm) ∧
      ∃ e : {Pm : base (T := T) ⟶ projModelCR xet.curve //
              (∃ (hP : Pm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom))
                 (hQ : Qm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom)),
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                   (Spec.map (CommRingCat.ofHom (ψ).toRingHom)) ⟨Pm, hP⟩ ⟨Qm, hQ⟩) ∧
              Spec.map (CommRingCat.ofHom resT) ≫ Pm =
                (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1} ≃
          {P : Section (xet.curve.map (ψ).toRingHom) //
            (∃ χ : OriginChartRing (xet.curve.map ψ.toRingHom) →+* T, ReducesToOrigin P χ (maximalIdeal T)) ∧
            IsDrinfeldBasis ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)) q P Q},
        ∀ (Pm : {Pm : base (T := T) ⟶ projModelCR xet.curve //
              (∃ (hP : Pm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom))
                 (hQ : Qm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom)),
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                   (Spec.map (CommRingCat.ofHom (ψ).toRingHom)) ⟨Pm, hP⟩ ⟨Qm, hQ⟩) ∧
              Spec.map (CommRingCat.ofHom resT) ≫ Pm =
                (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1})
          (φ : projModelGradingCR xet.curve →+*ᵍ projModelGradingCR (xet.curve.map ψ.toRingHom))
          (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (xet.curve.map ψ.toRingHom)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR xet.curve)).map φ),
          IsCoefficientHom xet.curve ψ.toRingHom φ → ((e Pm).1).1 ≫ Proj.map φ hφ = Pm.1 := by sorry
