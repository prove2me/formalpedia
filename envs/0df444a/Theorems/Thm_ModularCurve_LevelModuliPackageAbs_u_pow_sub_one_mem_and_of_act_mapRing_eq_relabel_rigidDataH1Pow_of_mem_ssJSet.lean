-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_rigidDataH1Pow_of_mem_ssJSet
-- name    : ModularCurve.LevelModuliPackageAbs.u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_rigidDataH1Pow_of_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/ee553a37-5b59-5fd2-9f08-e22dbea873ed
-- title:
--   Rigidity of the scalar of a relabelling automorphism at supersingular j
-- statement:
--   Data defining the moduli problem. Fix a prime $q$, a natural number $M'\neq 0$, a prime $\ell_g$ with $\ell_g\equiv 11 \pmod{12}$ and $\ell_g\mid M'$, and a commutative ring $A_0$. Three transport hypotheses are assumed for all $A_0$-algebras $T$: `hℓ`, that the predicate [`ModularCurve.IsGamma1Point W ℓg D`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) (the affine equation holds at $(x_P,y_P)$, $(\mathrm{pre}\Psi_{\ell_g}W)(x_P)=0$, $x_Q=x_P$ and $y_Q=y_P$) is preserved when a Weierstrass curve $W$ and a `LevelPData` $D$ are both moved by a variable change $C$; `hM`, that [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) (for $p^k=2$ the two-torsion condition `IsTwoKernel`, otherwise the cyclic-kernel generator conditions on $h$: degree at most $\varphi(p^k)/2$, leading coefficient $1$ in that degree, $h\cdot \mathrm{pre}\Psi_{p^{k-1}}\mid \mathrm{pre}\Psi_{p^{k}}$, and divisibility of the relevant $\mathrm{smulNumerator}$s) is preserved under the degree-twisted variable change `kernelVariableChangeDeg C (gamma0PowDeg p k)`; and `hL`, that divisibility $h\mid \mathrm{inLineMulPoly}\,W\,\ell_g\,n\,x$ is preserved by passing to `kernelVariableChangeDeg C d h` and to the transformed abscissa $u^{-2}(x-r)$. Further, $\mathcal G$ is a family of relative group laws on the projective models of curves with unit discriminant over $A_0$-algebras, assumed chord–tangent (`h𝒢`: a points-evaluation exists in each case) and origin-normalised (`h𝒢O`: the identity section is given by an origin chart killing `xOverY` and `zOverY`), and $\mathcal T$ is a level transport for $\mathcal G$ at $q$ satisfying `h𝒯`, which says that the variable-change and coefficient-change transports of a raw Drinfeld pair have the expected curve and that their two sections pull back to the original ones along any graded homomorphism of projective-model rings satisfying `IsVariableChangeHom` resp. `IsCoefficientHom`. It is assumed that $\ell_g$ is a unit in $A_0$ (`hℓA`), and that such graded homomorphisms exist: `hVC` provides, for every projective curve and variable change, a graded ring map $\varphi$ with `IsVariableChangeHom` whose image ideal dominates the irrelevant ideal, and `hCO` does the same for coefficient maps along $A_0$-algebra homomorphisms, with `IsCoefficientHom`.
--
--   These data assemble the rigid Weierstrass datum $\mathcal R=$ `rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯`, whose raw points over an $A_0$-algebra $T$ consist of a Weierstrass curve with unit discriminant together with level data in three slots — a family $(h_p)_{p\mid M'}$ of $\Gamma_0(p^{v_p(M')})$-kernel polynomials, a `LevelPData` $(x_P,y_P,x_Q,y_Q)$ which is a $\Gamma_1(\ell_g)$-point, and a raw Drinfeld pair (a projective curve with two sections) which is a level structure for $\mathcal G$ at $q$ — subject to the linking condition `IsGamma1Link`, namely that $h_{\ell_g}$ divides $\mathrm{inLineMulPoly}\,W\,\ell_g\,\ell_g^{v_{\ell_g}(M')-1}\,x_P$ whenever $\ell_g\mid M'$; points of the associated moduli datum are the classes of raw points modulo variable changes. Let $P_0$ be a `LevelModuliPackageAbs` for this datum, i.e. an $A_0$-algebra $B_0$ with a point `univ` over $B_0$ which represents the functor of points uniquely, and let $x$ be a raw point over $B_0$ whose class is `P₀.univ` (`hx`).
--
--   The deformation frame. Let $R$ be a noetherian local domain, complete for its maximal-ideal topology, an $A_0$-algebra, with an $A_0$-algebra map $\iota : B_0\to R$; let $k$ be a field of characteristic $q$ in which $\ell_g$ and $M'$ are nonzero, and $\mathrm{res}_R : R\to k$ a surjective ring map with kernel $\mathfrak m_R$. Let $W_0$ be a complete discrete valuation ring with $\mathfrak m_{W_0}=(q)$ and a surjection $\mathrm{res}_0 : W_0\to k$ with kernel $\mathfrak m_{W_0}$, together with $W_0$-algebra and $A_0$-algebra structures forming a scalar tower $A_0\to W_0\to R$ and satisfying $\mathrm{res}_R\circ(\text{structure map})=\mathrm{res}_0$ (`hresR₀`). The hypothesis `hfac` states the factoring property of $(R,\iota)$: for every artinian local $W_0$- and $A_0$-algebra $T$ compatible with the tower, every surjection $\mathrm{res}_T : T\to k$ with kernel $\mathfrak m_T$ lifting $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi : B_0\to T$ with $\mathrm{res}_T\circ\varphi=\mathrm{res}_R\circ\iota$, there is a unique $W_0$-algebra map $\Phi : R\to T$ with $\mathrm{res}_T\circ\Phi=\mathrm{res}_R$ and $\Phi\circ\iota=\varphi$.
--
--   Formal groups and charts. $F$ is a commutative formal group over $R$ whose power series is the fixed formal group law of the projective curve in the Drinfeld slot of $\mathcal R.\mathrm{mapRing}\,\iota\,x$ (`hFW`), and $F_0$ a commutative formal group over $k$ whose power series is that of the $\mathrm{res}_R$-reduction of the same curve (`hF₀W`), with `hF₀` asserting that $F_0$ has a Drinfeld basis at $q$ with parameters $0,0$ relative to the zero ideal, i.e. its $q$-th series is a unit multiple of the corresponding Drinfeld divisor. The hypothesis `hssJ` requires that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring map $k\to\Omega$, the image of $\mathrm{res}_R(\iota\,P_0.j_0)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is: every elliptic curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$. Ring maps $\chi_P,\chi_Q$ from the origin chart ring of that curve to $R$ are given such that the two sections $P$ and $Q$ of the Drinfeld slot reduce to the origin with respect to them modulo $\mathfrak m_R$ (`hP`, `hQ`: each $\chi$ is an origin-chart section for the given section, and both `originParam χ` and `originW χ` lie in $\mathfrak m_R$). Moreover $F$ base-changes along $\mathrm{res}_R$ to $F_0$ (`hBC`), $F$ has a Drinfeld basis at $q$ with parameters $\mathrm{originParam}\,\chi_P$, $\mathrm{originParam}\,\chi_Q$ relative to $\mathfrak m_R$ (`hDr`), these two parameters generate $\mathfrak m_R$ (`hmax`), and `huniv` expresses the universality of $R$ as a deformation ring for this situation: for every artinian local $W_0$-algebra $T$ with a surjection $\mathrm{res}_T$ onto $k$ with kernel $\mathfrak m_T$ lifting $\mathrm{res}_0$, every commutative formal group $G$ over $T$ base-changing to $F_0$, and every $y_0,y_1\in\mathfrak m_T$ such that $G$ has a Drinfeld basis at $q$ with parameters $y_0,y_1$ relative to $\mathfrak m_T$, there is a unique $W_0$-algebra map $\varphi : R\to T$ with $\mathrm{res}_T\circ\varphi=\mathrm{res}_R$ for which there exist a formal group $F'$ over $T$ that is the base change of $F$ along $\varphi$ and an isomorphism of formal group laws $\psi : F'\to G$ whose series has coefficients reducing to those of $X$ (the $n$-th coefficient reduces to $1$ for $n=1$ and to $0$ otherwise) and whose adic application sends $\varphi(\mathrm{originParam}\,\chi_P)$ to $y_0$ and $\varphi(\mathrm{originParam}\,\chi_Q)$ to $y_1$.
--
--   The relabelling automorphism. Let $\gamma\in\mathrm{SL}_2(\mathbb Z)$ lie in $\Gamma_0(M')$ and let $\rho_\gamma$ be an automorphism of the moduli problem (an operation on points, natural in the $A_0$-algebra, preserving $j$). The pinning hypothesis `hpin` says that over any field $T$ which is an $A_0$-algebra, and for raw points $y,y'$ over $T$ with $y$'s Drinfeld-slot curve of unit discriminant, $\rho_\gamma$ sends the class of $y$ to the class of $y'$ as soon as: the curves agree, the $\Gamma_0$-slots agree, the point attached to $(x_P,y_P)$ of $y'$ on the base change of $y$'s curve equals $\gamma_{00}$ times the corresponding point of $y$, $y'$ has $x_Q=x_P$ and $y_Q=y_P$, and the Drinfeld slot of $y'$ is the $\gamma$-relabelling `RawDrinfeldPair.relabel 𝒢 γ` of that of $y$ (the pair of $\mathbb Z$-linear combinations $\gamma_{00}P+\gamma_{10}Q$, $\gamma_{01}P+\gamma_{11}Q$ for the group law $\mathcal G$). The hypothesis `hfix` says that $\iota(P_0.\mathrm{classify}(\rho_\gamma.\mathrm{act}\,P_0.\mathrm{univ})\,b)-\iota(b)\in\mathfrak m_R$ for all $b\in B_0$. Let $\theta_0 : R\to R$ be a $W_0$-algebra endomorphism with $\theta_0(\iota\,b)=\iota(P_0.\mathrm{classify}(\rho_\gamma.\mathrm{act}\,P_0.\mathrm{univ})\,b)$ for all $b\in B_0$ (`hcompl`) and $\theta_0(r)-r\in\mathfrak m_R$ for all $r\in R$ (`hres`).
--
--   The comparison. Let $V$ be a variable change over $R$, assume the Drinfeld-slot curve of $\mathcal R.\mathrm{mapRing}\,\iota\,x$ has unit discriminant (`hΔ`), and let $x'$ be a raw point over $R$ obtained by applying $V$ to the $\theta_0$-transport of $\mathcal R.\mathrm{mapRing}\,\iota\,x$ (`hact`), with the same Weierstrass curve (`hcurve`), the same $\Gamma_0$-slot (`hlev1`), Drinfeld slot the $\gamma$-relabelling of the original one (`hlev22`), $\Gamma_1$-slot point satisfying, over the fraction field of $R$, that the point of $(x_P,y_P)$ of $x'$ equals $\gamma_{00}$ times the point of $(x_P,y_P)$ of $\mathcal R.\mathrm{mapRing}\,\iota\,x$ on the base change of the common curve (`hlev21`), and $x'$ having $x_Q=x_P$ and $y_Q=y_P$ (`hlev21'`).
--
--   Conclusion. Writing $u=V.u\in R^\times$ for the scaling unit of $V$, viewed in $R$, the following four statements hold: (i) $u^{q+1}-1\in\mathfrak m_R$; (ii) if the residue of the entry $\gamma_{11}$ in $\mathbb Z/\ell_g$ equals $1$, then $u-1\in\mathfrak m_R$; (iii) if that residue equals $-1$, then $u+1\in\mathfrak m_R$; and (iv) if $\gamma$ lies in the principal congruence subgroup $\Gamma(q)$, the residue of $\gamma_{11}$ in $\mathbb Z/\ell_g$ is not $1$, and in the case $q=2$ that residue is also not $-1$, then $u-1\notin\mathfrak m_R$.
--
--   This is the rigidity statement for the scalar part of the variable change that compares a $\gamma$-relabelled level datum with its transport along a residually trivial endomorphism $\theta_0$, at a closed point whose $j$-invariant is supersingular in characteristic $q$: the scalar is a $(q+1)$-st root of unity modulo $\mathfrak m_R$, is $\pm 1$ according to the $\Gamma_1(\ell_g)$-diamond entry $\gamma_{11}$ modulo $\ell_g$, and is non-trivial whenever that diamond is non-trivial and $\gamma\in\Gamma(q)$. It is used by [`ModularCurve.LevelModuliPackageAbs.exists_originParam_linearPart_of_algHom_comp_eq_classify_act_of_problemAut_relabel_rigidDataH1Pow_of_mem_ssJSet`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_originParam_linearPart_of_algHom_comp_eq_classify_act_of_problemAut_relabel_rigidDataH1Pow_of_mem_ssJSet), where the induced action on the Drinfeld origin parameters is computed to first order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_rigidDataH1Pow_of_mem_ssJSet.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] SubalgebraClass.toAlgebra
attribute [local instance 10001] AdicCompletion.instAlgebra

theorem ModularCurve.LevelModuliPackageAbs.u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_rigidDataH1Pow_of_mem_ssJSet
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
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

    (hℓA : IsUnit ((ℓg : ℕ) : A₀))
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]

    [IsDomain R]
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

    (F : FormalGroup R) [F.IsComm]
    (hFW : F.toPowerSeries =
      (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).formalGroupLawFixed)

    (F₀ : FormalGroup k) [F₀.IsComm]
    (hF₀W : F₀.toPowerSeries =
      ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR).formalGroupLawFixed)
    (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)

    (hssJ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (ιΩ : k →+* Ω),
      ιΩ (resR (ι P₀.j₀)) ∈ ModularCurve.ssJSet q Ω)

    (χP χQ : OriginChartRing ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve →+* R)
    (hP : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.P χP (maximalIdeal R))
    (hQ : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.Q χQ (maximalIdeal R))
    (hBC : F.IsBaseChange resR F₀)
    (hDr : F.IsDrinfeldBasisAdic (maximalIdeal R) q (originParam χP) (originParam χQ))
    (hmax : maximalIdeal R = Ideal.span {originParam χP, originParam χQ})
    (huniv : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
        ∀ (y₀ y₁ : T), y₀ ∈ maximalIdeal T → y₁ ∈ maximalIdeal T →
        G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁ →
          ∃! φ : R →ₐ[W₀] T, (∀ r : R, resT (φ r) = resR r) ∧
            ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' G),
              (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χP)) = y₀ ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χQ)) = y₁)

    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (ργ : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.ProblemAut)
    (hpin : ∀ (T : Type) [Field T] [DecidableEq T] [Algebra A₀ T]
        (y y' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y'.level.2.1.xP y'.level.2.1.yP =
          (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
            ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y.level.2.1.xP y.level.2.1.yP →
        y'.level.2.1.xQ = y'.level.2.1.xP → y'.level.2.1.yQ = y'.level.2.1.yP →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.2 hΔ →
        ργ.act (Quot.mk _ y) = Quot.mk _ y')
    (hfix : ∀ b : P₀.B₀, ι (P₀.classify (ργ.act P₀.univ) b) - ι b ∈ maximalIdeal R)

    (θ₀ : R →ₐ[W₀] R)
    (hcompl : ∀ b : P₀.B₀, θ₀ (ι b) = ι (P₀.classify (ργ.act P₀.univ) b))
    (hres : ∀ r : R, θ₀ r - r ∈ maximalIdeal R)

    (V : WeierstrassCurve.VariableChange R)
    (hΔ : IsUnit ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve.Δ)
    (x' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw R)
    (hact : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).act V ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x)) = x')
    (hcurve : x'.curve = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve)
    (hlev1 : x'.level.1 = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.1)
    (hlev22 : x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 hΔ)
    [DecidableEq (FractionRing R)]

    (hlev21 : ModularCurve.LevelRelabelling.toPoint ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve).baseChange (FractionRing R))
        (algebraMap R (FractionRing R) x'.level.2.1.xP) (algebraMap R (FractionRing R) x'.level.2.1.yP) =
      (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
        ModularCurve.LevelRelabelling.toPoint ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve).baseChange (FractionRing R))
          (algebraMap R (FractionRing R) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.1.xP) (algebraMap R (FractionRing R) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.1.yP))
    (hlev21' : x'.level.2.1.xQ = x'.level.2.1.xP ∧ x'.level.2.1.yQ = x'.level.2.1.yP) :
    (((V.u : Rˣ) : R) ^ (q + 1) - 1 ∈ maximalIdeal R) ∧

    (((γ 1 1 : ℤ) : ZMod ℓg) = 1 → ((V.u : Rˣ) : R) - 1 ∈ maximalIdeal R) ∧

    (((γ 1 1 : ℤ) : ZMod ℓg) = -1 → ((V.u : Rˣ) : R) + 1 ∈ maximalIdeal R) ∧

    (γ ∈ CongruenceSubgroup.Gamma q → ((γ 1 1 : ℤ) : ZMod ℓg) ≠ 1 →
      (q = 2 → ((γ 1 1 : ℤ) : ZMod ℓg) ≠ -1) →
      ((V.u : Rˣ) : R) - 1 ∉ maximalIdeal R) := by sorry
