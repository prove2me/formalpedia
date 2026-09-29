-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_equiv_algHom_symm_apply_eq_of_represents_nsmul_eq_one_of_factorsThrough_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_equiv_algHom_symm_apply_eq_of_represents_nsmul_eq_one_of_factorsThrough_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/1306a2c8-c374-506d-b10a-e82b1c308740
-- title:
--   Torsion-lift ring S represents pinned q-torsion points at level H₁
-- statement:
--   Throughout, $q$ is a prime, $\ell_g$ is a prime with $\ell_g \equiv 11 \pmod{12}$, $M'$ is a nonzero natural number, and $A_0$ is a commutative ring.
--
--   **Transport hypotheses over $A_0$.** Three hypotheses say that the three kinds of level data are carried along Weierstrass variable changes, for every $A_0$-algebra $T$, every Weierstrass curve $W$ over $T$ and every variable change $C$: `hℓ` states that if $D = (x_P,y_P,x_Q,y_Q)$ is a $\Gamma_1(\ell_g)$-point of $W$ — that is, $(x_P,y_P)$ satisfies the affine Weierstrass equation, $(W.\mathrm{pre}\Psi_{\ell_g})(x_P) = 0$, $x_Q = x_P$ and $y_Q = y_P$ — then `D.variableChange C` is a $\Gamma_1(\ell_g)$-point of $C \bullet W$; `hM` states that if a polynomial $h$ satisfies `IsGamma0PowAt W p k h` (for $p^k = 2$: $\deg h \le 1$, $h$ has coefficient $1$ in degree $1$, and $h \mid W.\Psi_2^2$; otherwise: $\deg h \le \varphi(p^k)/2$, the coefficient of $h$ in degree $\varphi(p^k)/2$ is $1$, $h \cdot W.\mathrm{pre}\Psi_{p^{k-1}} \mid W.\mathrm{pre}\Psi_{p^k}$, and $h$ divides $W.\mathrm{smulNumerator}\,a\,(\varphi(p^k)/2)\,h$ for all $a$ with $2 \le a \le (p^k-1)/2$ and $p \nmid a$), then `kernelVariableChangeDeg C (gamma0PowDeg p k) h`, namely $u^{-2d} \cdot h(u^2X + r)$ with $d =$ `gamma0PowDeg p k`, satisfies the same predicate for $C \bullet W$; `hL` states that divisibility $h \mid$ `inLineMulPoly W ℓg n x` is preserved, in the form `kernelVariableChangeDeg C d h` $\mid$ `inLineMulPoly (C • W) ℓg n (u⁻¹^2 (x - r))`.
--
--   **Group-law data over $A_0$.** $\mathcal G$ is a family `GroupLaws A₀` assigning to every $A_0$-algebra $T$, projective Weierstrass curve $W$ over $T$ and proof that $\Delta_W$ is a unit a relative group law on the projective model; `h𝒢` asserts that each such group law admits a points-evaluation (chord–tangent) description and `h𝒢O` that its unit section is cut out on the origin chart by a ring homomorphism killing $x/y$ and $z/y$. $\mathcal T$ is a `LevelTransport A₀ 𝒢 q`, i.e. functorial transport of raw Drinfeld pairs (curve together with two sections) along algebra maps and variable changes preserving the condition that the two sections form a Drinfeld basis of level $q$; `h𝒯` is the pinning condition `IsSectionTransport`, which says that the transported sections are the pullbacks of the original ones along the corresponding maps of projective models.
--
--   **The global package $P_0$.** `P₀` is an absolute level-moduli package over $A_0$ for the moduli datum attached to `rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯`: an $A_0$-algebra `P₀.B₀` with a point `P₀.univ` of the functor $T \mapsto$ (raw objects over $T$ modulo variable change), where a raw object consists of a Weierstrass curve with unit discriminant, a family of kernel polynomials indexed by the primes dividing $M'$ satisfying `IsGamma0PowAt` at the exact prime powers of $M'$, a $\Gamma_1(\ell_g)$-point, a Drinfeld basis of level $q$ for $\mathcal G$, and the link condition `IsGamma1Link` relating the $\ell_g$-component of the kernel family to `inLineMulPoly`; `represents` says every point over every $A_0$-algebra is the image of `P₀.univ` under a unique $A_0$-algebra map.
--
--   **Deformation-ring data.** $R$ is a Noetherian local $A_0$-algebra, complete for its maximal ideal, with an $A_0$-algebra map $\iota : P_0.B_0 \to R$; $k$ is a field of characteristic $q$ in which $\ell_g$ and $M'$ are invertible ($(\ell_g)_k \ne 0$, $(M')_k \ne 0$); $\mathrm{res}_R : R \to k$ is surjective with kernel the maximal ideal. $W_0$ is a complete discrete valuation ring which is a domain with maximal ideal $(q)$, equipped with a surjection $\mathrm{res}_0 : W_0 \to k$ whose kernel is its maximal ideal; $R$ is a $W_0$-algebra, $W_0$ an $A_0$-algebra, the tower $A_0 \to W_0 \to R$ commutes, and $\mathrm{res}_R$ restricts to $\mathrm{res}_0$ on $W_0$. The hypothesis `hfac` is the universal property of $(R,\iota)$: for every Artinian local $W_0$-algebra $T$ which is an $A_0$-algebra compatibly with the tower, and every surjection $\mathrm{res}_T : T \to k$ with kernel the maximal ideal and restricting to $\mathrm{res}_0$ on $W_0$, every $A_0$-algebra map $\varphi : P_0.B_0 \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R \circ \iota$ extends to a unique $W_0$-algebra map $\Phi : R \to T$ with $\mathrm{res}_T \circ \Phi = \mathrm{res}_R$ and $\Phi \circ \iota = \varphi$.
--
--   **Transport and group-law hypotheses over $W_0$.** The hypotheses `hℓ'`, `hM'`, `hL'` are the exact analogues of `hℓ`, `hM`, `hL` for $W_0$-algebras, and `h𝒢r`, `h𝒢Or` say that the restriction of scalars of $\mathcal G$ along $A_0 \to W_0$ is again chord–tangent with origin identity.
--
--   **The étale package.** `Pet` is an absolute level-moduli package over $W_0$ for the level component obtained as the product of `gamma0PowComponent W₀ M' hM'`, `gamma1Component W₀ ℓg hℓ'` and the trivial component, restricted along the predicate `IsGamma1Link` (the $q$-level slot being trivial), made rigid and turned into a moduli datum. The element `xet` is a raw object over `Pet.B₀` for this component — a Weierstrass curve `xet.curve` with unit discriminant, kernel polynomials `xet.level.1`, a $\Gamma_1(\ell_g)$-point `xet.level.2.1` and a trivial $q$-slot, together with the level conditions — and `hxet` says that its class in the quotient by variable changes is `Pet.univ`.
--
--   **The $q$-torsion ring.** $C_Q$ is a commutative ring which is both a `Pet.B₀`-algebra and a $W_0$-algebra compatibly; $Q_u$ is a morphism $\mathrm{Spec}\,C_Q \to$ `projModelCR xet.curve` over $\mathrm{Spec}$ of the structure map `Pet.B₀ → CQ`. The hypothesis `hQu` says that the $q$-fold multiple of $Q_u$ for the relative group law $(\mathcal G$ restricted to $W_0)$ at `Pet.B₀`, `xet.curve`, `xet.isUnit_Δ` is the unit section, and `hrep` says that $(C_Q, Q_u)$ represents $q$-torsion: for every `Pet.B₀`-algebra $T$ and every $T$-section $Q$ of the projective model, $[q]Q$ is the unit section if and only if there is a unique `Pet.B₀`-algebra map $\chi : C_Q \to T$ with $\mathrm{Spec}\,\chi$ followed by $Q_u$ equal to $Q$.
--
--   **The torsion-lift stalk $S$.** $S$ is a Noetherian local $W_0$-algebra, complete for its maximal ideal, with a $W_0$-algebra map $\iota_S : C_Q \to S$ and a surjection $\mathrm{res}_S : S \to k$ with kernel the maximal ideal and restricting to $\mathrm{res}_0$ on $W_0$; `hfacS` is the corresponding universal property: for every Artinian local $W_0$-algebra $T$ with a surjection $\mathrm{res}_T$ onto $k$ with kernel the maximal ideal and restricting to $\mathrm{res}_0$, every $W_0$-algebra map $\varphi : C_Q \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_S \circ \iota_S$ extends to a unique $W_0$-algebra map $\Phi : S \to T$ with $\mathrm{res}_T \circ \Phi = \mathrm{res}_S$ and $\Phi \circ \iota_S = \varphi$.
--
--   **Formal-group data.** $F_S$ is a formal group over $S$ whose power series is the formal group law `formalGroupLawFixed` of the base change of `xet.curve` along $\iota_S \circ (\text{structure map } Pet.B_0 \to C_Q)$; $g \in S[X]$ is monic of degree $q-1$ with all coefficients in degrees $< q-1$ in the maximal ideal of $S$ and constant term $q w$ for some unit $w$; $v$ is a unit power series; and `hfacq` states the factorisation of the $q$-th iterate series $F_S.\mathrm{nthSeries}\,q = X \cdot g \cdot v$.
--
--   **Residue-level data.** $k$ is an $A_0$-algebra, a $W_0$-algebra compatibly with the tower, and a `Pet.B₀`-algebra, with $\mathrm{alg}_{W_0 \to k} = \mathrm{res}_0$ (`hk₀`). The map $\rho : P_0.B_0 \to k$ is an $A_0$-algebra map with $\rho = \mathrm{res}_R \circ \iota$; $\psi^{\mathrm{et}} : Pet.B_0 \to k$ is a $W_0$-algebra map with $\psi^{\mathrm{et}} = \mathrm{res}_S \circ \iota_S \circ (Pet.B_0 \to C_Q)$, and it agrees with the $Pet.B_0$-algebra structure on $k$ (`hψalg`). The reduced curve `xet.curve.map ψet` has unit discriminant (`hΔk`), and $Q_k$ is a $k$-section of it; `hQk_pin` asserts the existence of a graded ring map $\phi$ from the projective-model grading of `xet.curve` to that of the reduced curve, subject to the irrelevant-ideal condition, which is a coefficient homomorphism along $\psi^{\mathrm{et}}$ and for which $Q_k$ followed by $\mathrm{Proj}(\phi)$ equals $\mathrm{Spec}(\mathrm{res}_S \circ \iota_S)$ followed by $Q_u$; `hQk` says $Q_k$ is not the unit section. Further, `hhk`, `hDk`, `hLk` say that the reductions along $\psi^{\mathrm{et}}$ of the kernel polynomials, of the $\Gamma_1(\ell_g)$-point and of the link condition hold for the reduced curve, and `hyk` says that the raw Drinfeld pair consisting of the reduced curve with first section the unit section and second section $Q_k$ is of level $q$ for $\mathcal G$ (its curve is the given one and the two sections form a Drinfeld basis of level $q$). Finally, `hρyk` says that the image of `P₀.univ` under $\rho$ is the class of the explicit raw object over $k$ built from the reduced curve, its unit discriminant, the reduced kernel family, the reduced $\Gamma_1(\ell_g)$-point, the pair $(O, Q_k)$, and the level proofs $\langle\langle$`hhk`, `hDk`, `hyk`$\rangle$, `hLk`$\rangle$.
--
--   **Conclusion.** There exists a family $\beta$ which assigns to every Artinian local $W_0$-algebra $T$ and every surjection $\mathrm{res}_T : T \to k$ with kernel the maximal ideal of $T$ and with $\mathrm{res}_T \circ \mathrm{alg}_{W_0 \to T} = \mathrm{res}_0$ a bijection
--   $$\beta : \Bigl\{\, d \in (Pet.B_0 \to_{W_0} T) \times \bigl(\mathrm{Spec}\,T \longrightarrow \mathtt{projModelCR xet.curve}\bigr) \ \Bigm|\ (\mathrm i),(\mathrm{ii}),(\mathrm{iii}) \,\Bigr\} \ \simeq\ (S \to_{W_0} T),$$
--   where the three conditions on $d = (d_1, d_2)$ are: (i) $\mathrm{res}_T(d_1 b) = \psi^{\mathrm{et}}(b)$ for all $b \in Pet.B_0$; (ii) there is a proof that $d_2$ followed by the structure morphism `projModelStrCR xet.curve` equals $\mathrm{Spec}$ of $d_1$, and the resulting section $\langle d_2, \cdot\rangle$ has $q$-fold multiple equal to the unit section for the relative group law $(\mathcal G$ restricted to $W_0)$ at `Pet.B₀`, `xet.curve`, `xet.isUnit_Δ`; (iii) $\mathrm{Spec}(\mathrm{res}_T)$ followed by $d_2$ equals $\mathrm{Spec}(\mathrm{res}_S \circ \iota_S)$ followed by $Q_u$.
--
--   Moreover, for every such $T$, $\mathrm{res}_T$ and every $W_0$-algebra map $\Phi : S \to T$, the pair underlying $\beta^{-1}(\Phi)$ is computed explicitly:
--   $$\bigl(\beta^{-1}(\Phi)\bigr)_{\text{pair}} = \bigl(\ \Phi \circ \iota_S \circ (Pet.B_0 \to C_Q),\ \ \mathrm{Spec}(\Phi \circ \iota_S) \text{ followed by } Q_u \ \bigr),$$
--   the first component being the composite $W_0$-algebra map $Pet.B_0 \to C_Q \to S \to T$ and the second the pullback of the universal $q$-torsion section $Q_u$ along $\Phi \circ \iota_S$.
--
--   This is the pro-Yoneda identification of the torsion-lift stalk at level $H_1 = \Gamma_0(M') \cap \Gamma_1(\ell_g)$ together with Drinfeld $\Gamma(q)$-structure: on Artinian local $W_0$-algebras, the functor of pairs consisting of a point of the étale package pinned to $\psi^{\mathrm{et}}$ and a $q$-torsion section of the universal curve pinned to the reduction of $Q_u$ is identified with $\operatorname{Hom}_{W_0\text{-alg}}(S,-)$, naturally and by an explicit pullback formula. It feeds the next step, which uses the factorisation of the $q$-division series of the formal group to identify these $S$-points with roots of the degree $q-1$ factor $g$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_equiv_algHom_symm_apply_eq_of_represents_nsmul_eq_one_of_factorsThrough_rigidDataH1Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.exists_equiv_algHom_symm_apply_eq_of_represents_nsmul_eq_one_of_factorsThrough_rigidDataH1Pow
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
    ∃ β : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w),
          {d : (Pet.B₀ →ₐ[W₀] T) × (base (T := T) ⟶ projModelCR xet.curve) //
            (∀ b : Pet.B₀, resT (d.1 b) = ψet b) ∧
            (∃ hQ : d.2 ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom d.1.toRingHom),
              ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q ⟨d.2, hQ⟩ =
                ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _) ∧
            Spec.map (CommRingCat.ofHom resT) ≫ d.2 =
              Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1} ≃ (S →ₐ[W₀] T),
      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) (Φ : S →ₐ[W₀] T),
          (((β T resT hT₁ hT₂ hT₃).symm Φ).1 :
              (Pet.B₀ →ₐ[W₀] T) × (base (T := T) ⟶ projModelCR xet.curve)) =
            ((Φ.comp ιS).comp (IsScalarTower.toAlgHom W₀ Pet.B₀ CQ),
              Spec.map (CommRingCat.ofHom (Φ.toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1) := by sorry
