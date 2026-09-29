-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_ringEquiv_originParam_linearPart_of_problemAut_relabel_of_reducesToOrigin_universal_gamma0Pow_of_mem_ssJSet
-- name    : ModularCurve.LevelModuliPackageAbs.exists_ringEquiv_originParam_linearPart_of_problemAut_relabel_of_reducesToOrigin_universal_gamma0Pow_of_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/c81a3fa9-52fa-5756-b9c6-7b9f27b13e8b
-- title:
--   Level relabelling on the deformation ring: linear part cγ̄
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ and a nonzero natural number $M'$, and a commutative base ring $A_0$ in which $\ell$ is invertible. The hypotheses `hℓ` and `hM` say that level-$\ell$ structures (in the sense of `IsLevelPStructure`: two affine points on the curve, both with $x$-coordinate a root of $\mathrm{pre}\Psi_\ell$, and with both independence elements `indepElt` units) and the polynomials cutting out cyclic $p^k$-kernels (`IsGamma0PowAt`) transport along Weierstrass variable changes; `𝒢` is a family of relative group laws on the projective models of curves with unit discriminant, chord-tangent and with identity section given by an origin chart, and `𝒯` is a transport of Drinfeld pairs compatible with the variable-change and coefficient maps of the graded projective-model rings, whose existence for all curves is hypothesised in `hVC` and `hCO`. Let $D$ be the level moduli datum attached to `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯`, i.e. Weierstrass curves with unit discriminant carrying a $\Gamma_0$-type kernel polynomial at each prime factor of $M'$, a level-$\ell$ datum and a Drinfeld basis of level $q$, up to variable change, and let $P_0$ be a fine moduli package for $D$: a ring $B_0$ with a universal point whose classifying maps are unique. Let $x$ be a raw representative of that universal point. Let $R$ be a complete noetherian local domain, an $A_0$-algebra, with $A_0$-algebra map $\iota : B_0 \to R$, residue field $k$ of characteristic $q$ in which $\ell$ and $M'$ are nonzero, presented by a surjection $\mathrm{res}_R$ with kernel the maximal ideal; let $W_0$ be a complete discrete valuation ring with maximal ideal $(q)$ and residue field $k$, with $R$ a $W_0$-algebra compatibly over $A_0$ and over $k$. The hypothesis `hfac` states that every residue-compatible $A_0$-algebra map $B_0 \to T$ into an Artinian local $W_0$-algebra $T$ with residue field $k$ extends uniquely to a residue-compatible $W_0$-algebra map $R \to T$ through $\iota$. Let $F$ be the commutative formal group over $R$ given by the formal group law of the curve of $\iota_*x$, let $F_0$ be its reduction over $k$, assumed to satisfy `IsDrinfeldBasisAdic ⊥ q 0 0`, and assume $F$ is the base change of $F_0$ along $\mathrm{res}_R$. Assume that for every algebraically closed field $\Omega$ of characteristic $q$ and every embedding $k \to \Omega$ the image of $\mathrm{res}_R(\iota(P_0.j_0))$ lies in `ssJSet q Ω`, that is, every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero $q$-torsion point. Let $\chi_P, \chi_Q$ be ring maps from the origin chart ring of the universal curve to $R$ which are origin-chart sections for the universal Drinfeld sections $P$ and $Q$ with both origin coordinates in the maximal ideal, put $x_0 = \mathrm{originParam}\,\chi_P$, $x_1 = \mathrm{originParam}\,\chi_Q$, and assume $F$ has a Drinfeld basis of level $q$ at $(x_0,x_1)$ relative to $\mathfrak m_R$, that $\mathfrak m_R = (x_0,x_1)$, and that $(R,F,x_0,x_1)$ is universal (`huniv`) among deformations of $F_0$ with a Drinfeld basis of level $q$ over Artinian local $W_0$-algebras with residue field $k$, up to an isomorphism of formal group laws reducing to the identity. Finally let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$, let $\rho_\gamma$ be an automorphism of the moduli problem $D$ which on points over fields relabels both the level-$\ell$ datum and the Drinfeld pair by $\gamma$ (`hpin`), and assume the induced endomorphism $P_0.\mathrm{classify}(\rho_\gamma \cdot \mathrm{univ})$ of $B_0$ becomes congruent to the identity modulo $\mathfrak m_R$ after applying $\iota$. The conclusion asserts the existence of a ring automorphism $\theta_0$ of $R$ and of $c \in R$ such that $\theta_0 \circ \iota = \iota \circ P_0.\mathrm{classify}(\rho_\gamma \cdot \mathrm{univ})$ on $B_0$, $\theta_0$ fixes the image of $W_0$, $\theta_0(r) \equiv r \bmod \mathfrak m_R$ for all $r$, and modulo $\mathfrak m_R^2$ one has $\theta_0(x_0) \equiv c(\gamma_{00}x_0 + \gamma_{10}x_1)$ and $\theta_0(x_1) \equiv c(\gamma_{01}x_0 + \gamma_{11}x_1)$; moreover $c^{q+1} \equiv 1 \bmod \mathfrak m_R$, $c \equiv 1 \bmod \mathfrak m_R$ whenever $\gamma \in \Gamma(\ell)$, and $c \not\equiv 1 \bmod \mathfrak m_R$ whenever $\gamma \in \Gamma(q)$ but $\gamma \notin \Gamma(\ell)$.
--
--   This is the deformation-theoretic functoriality of level relabelling at a supersingular point of the fine moduli problem with $\Gamma_0(M')$, level-$\ell$ and Drinfeld level-$q$ structure: the automorphism $\rho_\gamma$ of the moduli problem is realised as an automorphism of the universal deformation ring $R$, congruent to the identity on residues, whose effect on the two Drinfeld parameters is, to first order, the matrix $\gamma$ scaled by a single unit $c$ with $c^{q+1} \equiv 1$. It feeds the computation of the Drinfeld-basis deformation ring as a regular local ring with its Hasse parameter and relabelling action, used in the analysis of the $q$-adic geometry of the relevant modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_ringEquiv_originParam_linearPart_of_problemAut_relabel_of_reducesToOrigin_universal_gamma0Pow_of_mem_ssJSet.lean

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

theorem ModularCurve.LevelModuliPackageAbs.exists_ringEquiv_originParam_linearPart_of_problemAut_relabel_of_reducesToOrigin_universal_gamma0Pow_of_mem_ssJSet
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
    (hfix : ∀ b : P₀.B₀, ι (P₀.classify (ργ.act P₀.univ) b) - ι b ∈ maximalIdeal R) :
    ∃ (θ₀ : R ≃+* R) (c : R),

      (∀ b : P₀.B₀, θ₀ (ι b) = ι (P₀.classify (ργ.act P₀.univ) b)) ∧

      (∀ w : W₀, θ₀ (algebraMap W₀ R w) = algebraMap W₀ R w) ∧

      (∀ r : R, θ₀ r - r ∈ maximalIdeal R) ∧

      (θ₀ (originParam χP) - c * (((γ 0 0 : ℤ) : R) * originParam χP + ((γ 1 0 : ℤ) : R) * originParam χQ) ∈ (maximalIdeal R) ^ 2) ∧
      (θ₀ (originParam χQ) - c * (((γ 0 1 : ℤ) : R) * originParam χP + ((γ 1 1 : ℤ) : R) * originParam χQ) ∈ (maximalIdeal R) ^ 2) ∧

      (c ^ (q + 1) - 1 ∈ maximalIdeal R) ∧
      (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ maximalIdeal R) ∧
      (γ ∈ CongruenceSubgroup.Gamma q → γ ∉ CongruenceSubgroup.Gamma ℓ → c - 1 ∉ maximalIdeal R) := by sorry
