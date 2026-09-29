-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_originParam_linearPart_of_algHom_comp_eq_classify_act_of_problemAut_relabel_gamma0Pow_of_mem_ssJSet
-- name    : ModularCurve.LevelModuliPackageAbs.exists_originParam_linearPart_of_algHom_comp_eq_classify_act_of_problemAut_relabel_gamma0Pow_of_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/27894b17-0d25-5438-aeba-c4836a826e69
-- title:
--   Linear part of the relabelling endomorphism on Drinfeld parameters
-- statement:
--   Fix a prime $q$ with $q \neq 2$ and $5 \le q$, a prime $\ell$ with $3 \le \ell$, a nonzero natural number $M'$, and a commutative ring $A_0$ in which $\ell$ is invertible. Assume: the level-$\ell$ Katz structures (a pair of affine points satisfying the Weierstrass equation, with $\mathrm{preΨ}\,\ell$ vanishing at both $x$-coordinates and both independence elements `indepElt` units) are stable under variable change, and likewise the predicates `IsGamma0PowAt` under `kernelVariableChangeDeg`; a family $\mathcal{G}$ of relative group laws on projective models of curves with unit discriminant, chord–tangent and with origin-identity sections; a level transport $\mathcal{T}$ for $\mathcal{G}$ at $q$ satisfying `IsSectionTransport`; and the existence of graded ring homomorphisms on `projModelGradingCR` realising variable changes (`IsVariableChangeHom`) and coefficient maps (`IsCoefficientHom`), with irrelevant ideals dominated. Let $P_0$ be an abstract moduli package for the rigid data `rigidDataPow` assembled from the $\Gamma_0(M')$-power component, the level-$\ell$ component and the Drinfeld level-$q$ component, with coordinate ring $B_0$ and universal point, and let $x$ be a raw object over $B_0$ whose class is that universal point. Let $R$ be a noetherian local domain, adically complete for its maximal ideal, an $A_0$-algebra, with $\iota : B_0 \to R$, residue field $k$ of characteristic $q$ in which $\ell$ and $M'$ are nonzero, via a surjection $\mathrm{res}_R$ with kernel $\mathfrak{m}_R$; let $W_0$ be a complete discrete valuation domain with maximal ideal $(q)$ and residue map onto $k$, with $R$ a $W_0$-algebra compatibly over $A_0$ and over $k$. Assume $(R,\iota)$ is universal among artinian local $W_0$-algebras $T$ with residue map to $k$: every $A_0$-algebra map $B_0 \to T$ reducing to $\mathrm{res}_R \circ \iota$ extends uniquely to a $W_0$-algebra map $R \to T$ compatible with residues. Let $F$ be a commutative formal group over $R$ whose law is the formal group law of the curve of the Drinfeld component of $\iota_*x$, let $F_0$ over $k$ be the corresponding reduced formal group, assumed to be `IsDrinfeldBasisAdic` for the zero ideal with parameters $0,0$, and assume $F_0$ is the base change of $F$ along $\mathrm{res}_R$. Assume the residue of $\iota(\mathrm{P₀.j₀})$ is supersingular, in the sense that its image under any embedding of $k$ into an algebraically closed field $\Omega$ of characteristic $q$ lies in `ssJSet q Ω`: every elliptic curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$. Let $\chi_P, \chi_Q$ be ring homomorphisms from the origin chart ring of that curve to $R$ which are origin chart sections for the two sections $P,Q$ of the Drinfeld pair with both `originParam` and `originW` in $\mathfrak{m}_R$; write $x_0 = \mathrm{originParam}\,\chi_P$, $x_1 = \mathrm{originParam}\,\chi_Q$, and assume $F$ is a Drinfeld basis at $\mathfrak{m}_R$ for $q$ with parameters $x_0, x_1$, that $\mathfrak{m}_R = (x_0,x_1)$, and that $R$ is universal for such data: for every artinian local $W_0$-algebra $T$ with residue map to $k$, every commutative formal group $G$ over $T$ obtained from $F_0$ by base change, and every $y_0,y_1 \in \mathfrak{m}_T$ forming a Drinfeld basis for $G$, there is a unique residue-compatible $W_0$-algebra map $\varphi : R \to T$ together with a base change $F'$ of $F$ along $\varphi$ and an isomorphism of formal group laws $\psi : F' \to G$ whose series reduces to the identity and which carries $\varphi(x_0), \varphi(x_1)$ to $y_0, y_1$. Finally let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$, let $\rho_\gamma$ be an automorphism of the moduli problem pinned over fields by $\gamma$-relabelling (on field-valued raw points with unit discriminant, the curve and the $\Gamma_0(M')$-component unchanged, the level-$\ell$ data given by `LevelPData.relabel` and the Drinfeld pair by `RawDrinfeldPair.relabel` with matrix $\gamma$), suppose the classifying map of $\rho_\gamma$ applied to the universal point agrees with $\iota$ modulo $\mathfrak{m}_R$, and let $\theta_0 : R \to R$ be a $W_0$-algebra map with $\theta_0 \circ \iota = \iota \circ P_0.\mathrm{classify}(\rho_\gamma.\mathrm{act}\,P_0.\mathrm{univ})$ and $\theta_0 \equiv \mathrm{id}$ modulo $\mathfrak{m}_R$. Then there exists $c \in R$ with $\theta_0(x_0) \equiv c(\gamma_{00}x_0 + \gamma_{10}x_1)$ and $\theta_0(x_1) \equiv c(\gamma_{01}x_0 + \gamma_{11}x_1)$ modulo $\mathfrak{m}_R^2$, with $c^{q+1} \equiv 1 \pmod{\mathfrak{m}_R}$, with $c \equiv 1 \pmod{\mathfrak{m}_R}$ whenever $\gamma \in \Gamma(\ell)$, and with $c \not\equiv 1 \pmod{\mathfrak{m}_R}$ whenever $\gamma \in \Gamma(q)$ but $\gamma \notin \Gamma(\ell)$.
--
--   This is the computational half of the functoriality of the Drinfeld-level deformation ring at a supersingular point under relabelling of the level structure, in the style of Katz–Mazur: the induced endomorphism of $R$ acts on the Drinfeld parameters, to first order, by the matrix $\gamma$ scaled by a single unit $c$ whose residue satisfies $c^{q+1} = 1$ and which detects whether $\gamma$ lies in $\Gamma(\ell)$. It feeds the construction of the corresponding ring isomorphism of the deformation ring attached to the relabelling automorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_originParam_linearPart_of_algHom_comp_eq_classify_act_of_problemAut_relabel_gamma0Pow_of_mem_ssJSet.lean

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
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_originParam_linearPart_of_algHom_comp_eq_classify_act_of_problemAut_relabel_gamma0Pow_of_mem_ssJSet
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hq : 5 ≤ q) (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hℓA : IsUnit ((ℓ : ℕ) : A₀))
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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]

    [IsDomain R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
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
        ∀ φ : P₀.B₀ →ₐ[A₀] T, (∀ b : P₀.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : P₀.B₀, Φ (ι b) = φ b)

    (F : FormalGroup R) [F.IsComm]
    (hFW : F.toPowerSeries =
      (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).formalGroupLawFixed)

    (F₀ : FormalGroup k) [F₀.IsComm]
    (hF₀W : F₀.toPowerSeries =
      ((((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR).formalGroupLawFixed)
    (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)

    (hssJ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (ιΩ : k →+* Ω),
      ιΩ (resR (ι P₀.j₀)) ∈ ModularCurve.ssJSet q Ω)

    (χP χQ : OriginChartRing ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve →+* R)
    (hP : ReducesToOrigin ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.P χP (maximalIdeal R))
    (hQ : ReducesToOrigin ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.Q χQ (maximalIdeal R))
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
    (ργ : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut)
    (hpin : ∀ (T : Type) [Field T] [Algebra A₀ T]
        (y y' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        y'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel y.curve ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.1 →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.2 hΔ →
        ργ.act (Quot.mk _ y) = Quot.mk _ y')
    (hfix : ∀ b : P₀.B₀, ι (P₀.classify (ργ.act P₀.univ) b) - ι b ∈ maximalIdeal R)

    (θ₀ : R →ₐ[W₀] R)
    (hcompl : ∀ b : P₀.B₀, θ₀ (ι b) = ι (P₀.classify (ργ.act P₀.univ) b))
    (hres : ∀ r : R, θ₀ r - r ∈ maximalIdeal R) :
    ∃ c : R,

      (θ₀ (originParam χP) - c * (((γ 0 0 : ℤ) : R) * originParam χP + ((γ 1 0 : ℤ) : R) * originParam χQ) ∈ (maximalIdeal R) ^ 2) ∧
      (θ₀ (originParam χQ) - c * (((γ 0 1 : ℤ) : R) * originParam χP + ((γ 1 1 : ℤ) : R) * originParam χQ) ∈ (maximalIdeal R) ^ 2) ∧
      (c ^ (q + 1) - 1 ∈ maximalIdeal R) ∧
      (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ maximalIdeal R) ∧
      (γ ∈ CongruenceSubgroup.Gamma q → γ ∉ CongruenceSubgroup.Gamma ℓ → c - 1 ∉ maximalIdeal R) := by sorry
