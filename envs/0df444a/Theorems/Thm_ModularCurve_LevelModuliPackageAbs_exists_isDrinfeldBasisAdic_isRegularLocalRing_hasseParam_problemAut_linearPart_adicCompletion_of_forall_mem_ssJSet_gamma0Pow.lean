-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_problemAut_linearPart_adicCompletion_of_forall_mem_ssJSet_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_problemAut_linearPart_adicCompletion_of_forall_mem_ssJSet_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/b3123fcb-55c9-58f7-a96e-452974cab69d
-- title:
--   Complete local ring at a supersingular point, with level relabelling
-- statement:
--   Fix a prime $q\ge 5$, a nonzero $M'$ with $q\nmid M'$, and a prime $\ell\ge 3$ with $\ell\ne q$. Let $A_0$ be a discrete valuation domain with $\mathfrak m_{A_0}=(q)$ and finite residue field, in which $\ell$ and $M'$ are units. Assume: level-$\ell$ structures and $\Gamma_0(p^k)$-kernel polynomials transport along Weierstrass variable changes (`hℓ`, `hM`); $\mathcal G$ is a family of relative group laws on the projective models of $A_0$-algebra Weierstrass curves with unit discriminant that is chord–tangent and has the origin as identity; $\mathcal T$ is a level transport for $(\mathcal G,q)$ satisfying `IsSectionTransport`; and graded ring maps realising variable changes and coefficient changes on projective-model graded rings exist, compatibly with the irrelevant ideals (`hVC`, `hCO`). Let $P_0$ be a fine moduli package for the level moduli datum of `rigidDataPow A₀ ℓ M' q …`, that is, for the functor of Weierstrass curves with unit discriminant equipped with cyclic-kernel polynomials at the prime powers dividing $M'$, a level-$\ell$ datum and a Drinfeld $q$-basis pair, with universal object `P₀.univ` over $B_0 =$ `P₀.B₀`, of finite type over $A_0$. Let $\mathfrak p\subset B_0$ be maximal with $q\in\mathfrak p$ such that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring map $\varphi:B_0\to\Omega$ with kernel $\mathfrak p$, the value $\varphi(j_0)$ of the universal $j$-invariant lies in `ssJSet q Ω`: every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero $q$-torsion point. Put $R_0=$ `AdicCompletion 𝔭 B₀`. The conclusion asserts the existence of: instances making $R_0$ a Noetherian local ring, complete for its maximal ideal, with finite residue field of characteristic $q$; a complete discrete valuation domain $W_0$ with $\mathfrak m_{W_0}=(q)$, an $A_0$-algebra, together with a local algebra map $W_0\to R_0$ and scalar towers $A_0\to B_0\to R_0$ and $A_0\to W_0\to R_0$; a commutative formal group $F$ over $R_0$ and $x_0,x_1\in R_0$ such that `F.IsDrinfeldBasisAdic` holds for $\mathfrak m_{R_0}$, $q$, $x_0$, $x_1$, i.e. the $q$-th iterate series `F.nthSeries q` is a unit multiple of the Drinfeld divisor of $(x_0,x_1)$, and $\mathfrak m_{R_0}=(x_0,x_1)$; elements $T$ and a unit $w$ with $\operatorname{coeff}_q(\,$`F.nthSeries q`$\,)-wT\in (q)$; and $a_0\in W_0$, $k\ge 1$, a unit $w'$, such that $R_0$ is a regular local ring of Krull dimension $2$, the image of $j_0$ satisfies $j_0-a_0=w'T^k$ in $R_0$, and, for every $\gamma\in SL(2,\mathbb Z)$ lying in $\Gamma_0(M')$ and every automorphism $\rho_\gamma$ of the moduli problem (an endomorphism natural in the base $A_0$-algebra and preserving $j$) which on points over fields sends the class of a raw object $x$ with unit discriminant to the class of any $x'$ with the same curve and same $\Gamma_0(M')$-component whose level-$\ell$ datum is `LevelPData.relabel` of $x$'s by the integral matrix $\gamma$ and whose Drinfeld pair is `RawDrinfeldPair.relabel 𝒢` of $x$'s by $\gamma$, and whose induced endomorphism $\rho_B=$ `P₀.classify (ργ.act P₀.univ)` of $B_0$ satisfies $\rho_B(b)-b\in\mathfrak p$ for all $b$: there are a ring automorphism $\theta_0$ of $R_0$ and $c\in R_0$ with $\theta_0\circ(B_0\to R_0)=(B_0\to R_0)\circ\rho_B$, $\theta_0(r)\equiv r \pmod{\mathfrak m_{R_0}}$ for all $r$, $\theta_0(x_0)\equiv c(\gamma_{00}x_0+\gamma_{10}x_1)$ and $\theta_0(x_1)\equiv c(\gamma_{01}x_0+\gamma_{11}x_1)$ modulo $\mathfrak m_{R_0}^2$, $c^{q+1}\equiv 1$ modulo $\mathfrak m_{R_0}$, with $c\equiv 1$ modulo $\mathfrak m_{R_0}$ when $\gamma\in\Gamma(\ell)$, and $c-1\notin\mathfrak m_{R_0}$ when $\gamma\in\Gamma(q)$ but $\gamma\notin\Gamma(\ell)$.
--
--   This is the local structure theorem, in the style of Katz–Mazur, for the fine moduli problem of elliptic curves with $\Gamma_0(M')$, level-$\ell$ and Drinfeld level-$q$ data at a supersingular point of characteristic $q$: the completed local ring is regular of dimension two, carries a Drinfeld basis for the formal group and a Hasse parameter measuring the distance of $j$ from its residue value, and the relabelling automorphisms of the level data by matrices in $\Gamma_0(M')$ act on the Drinfeld basis through a scalar $c$ with $c^{q+1}=1$, nontrivial exactly on the part of the relabelling that is trivial at level $\ell$. It is used in the construction of the completed stalk of the full-level moduli scheme with its level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_problemAut_linearPart_adicCompletion_of_forall_mem_ssJSet_gamma0Pow.lean

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

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_problemAut_linearPart_adicCompletion_of_forall_mem_ssJSet_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q)

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)}) [Finite (IsLocalRing.ResidueField A₀)]

    (hℓA : IsUnit ((ℓ : ℕ) : A₀)) (hM'A : IsUnit ((M' : ℕ) : A₀))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

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
    [Algebra.FiniteType A₀ P₀.B₀]

    (𝔭 : Ideal P₀.B₀) [𝔭.IsMaximal] (hq𝔭 : algebraMap A₀ P₀.B₀ (q : A₀) ∈ 𝔭)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (φ : P₀.B₀ →+* Ω),
      RingHom.ker φ = 𝔭 → φ P₀.j₀ ∈ ModularCurve.ssJSet q Ω) :
    letI R₀ := AdicCompletion 𝔭 P₀.B₀
    ∃ (_ : IsLocalRing R₀) (_ : IsNoetherianRing R₀) (_ : IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀)
      (_ : Finite (IsLocalRing.ResidueField R₀)) (_ : CharP (IsLocalRing.ResidueField R₀) q)

      (W₀ : Type) (_ : CommRing W₀) (_ : IsDomain W₀) (_ : IsDiscreteValuationRing W₀)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀) (_ : IsLocalRing.maximalIdeal W₀ = Ideal.span {(q : W₀)})
      (_ : IsScalarTower A₀ P₀.B₀ R₀)
      (_ : Algebra W₀ R₀) (_ : Algebra A₀ W₀) (_ : IsScalarTower A₀ W₀ R₀) (_ : IsLocalHom (algebraMap W₀ R₀))

      (F : FormalGroup R₀) (_ : F.IsComm) (x₀ x₁ : R₀)
      (_ : F.IsDrinfeldBasisAdic (IsLocalRing.maximalIdeal R₀) q x₀ x₁)
      (_ : IsLocalRing.maximalIdeal R₀ = Ideal.span {x₀, x₁})

      (T : R₀) (w : R₀) (_ : IsUnit w)
      (_ : PowerSeries.coeff q (F.nthSeries q) - w * T ∈ Ideal.span {(q : R₀)})
      (a₀ : W₀) (k : ℕ) (_ : 1 ≤ k) (w' : R₀) (_ : IsUnit w'),
      IsRegularLocalRing R₀ ∧ ringKrullDim R₀ = 2 ∧
      algebraMap P₀.B₀ R₀ P₀.j₀ - algebraMap W₀ R₀ a₀ = w' * T ^ k ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ ργ : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut,
          (∀ (T : Type) [Field T] [Algebra A₀ T]
              (x x' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
              x'.curve = x.curve →
              x'.level.1 = x.level.1 →
              x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve
                ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
              x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
                ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
              ργ.act (Quot.mk _ x) = Quot.mk _ x') →
          (∀ b : P₀.B₀, P₀.classify (ργ.act P₀.univ) b - b ∈ 𝔭) →
            ∃ (θ₀ : R₀ ≃+* R₀) (c : R₀),

              (∀ b : P₀.B₀, θ₀ (algebraMap P₀.B₀ R₀ b) = algebraMap P₀.B₀ R₀ (P₀.classify (ργ.act P₀.univ) b)) ∧

              (∀ r : R₀, θ₀ r - r ∈ IsLocalRing.maximalIdeal R₀) ∧

              (θ₀ x₀ - c * (((γ 0 0 : ℤ) : R₀) * x₀ + ((γ 1 0 : ℤ) : R₀) * x₁) ∈ (IsLocalRing.maximalIdeal R₀) ^ 2) ∧
              (θ₀ x₁ - c * (((γ 0 1 : ℤ) : R₀) * x₀ + ((γ 1 1 : ℤ) : R₀) * x₁) ∈ (IsLocalRing.maximalIdeal R₀) ^ 2) ∧
              (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal R₀) ∧
              (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal R₀) ∧

              (γ ∈ CongruenceSubgroup.Gamma q → γ ∉ CongruenceSubgroup.Gamma ℓ →
                c - 1 ∉ IsLocalRing.maximalIdeal R₀)) := by sorry
