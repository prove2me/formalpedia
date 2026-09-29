-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_problemAut_linearPart_adicCompletion_of_forall_mem_ssJSet_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_problemAut_linearPart_adicCompletion_of_forall_mem_ssJSet_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/82d94789-7bba-5e27-9121-41d84b4d64d6
-- title:
--   Supersingular completion: Drinfeld basis, Hasse parameter, relabelling linear part
-- statement:
--   Fix a prime $q$, a nonzero $M'$ with $q \nmid M'$, and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Let $A_0$ be a discrete valuation domain with finite residue field and maximal ideal $(q)$, in which $\ell_g$ and $M'$ are units. Assume the three variable-change compatibilities $h\ell$, $hM$, $hL$ (the $\Gamma_1(\ell_g)$-point condition, the $\Gamma_0(p^k)$-kernel condition `IsGamma0PowAt`, and divisibility of `inLineMulPoly` are preserved by `VariableChange` and `kernelVariableChangeDeg`), let $\mathcal G$ be a family of relative group laws on the projective models which is chord-tangent and has the origin as identity, let $\mathcal T$ be a level transport for $\mathcal G$ at $q$ satisfying `IsSectionTransport`, and assume the graded-ring hypotheses `hVC`, `hCO` providing variable-change and coefficient homomorphisms of `projModelGradingCR` surjective onto the irrelevant ideal. Let $P_0$ be a fine moduli package for the level moduli datum of `rigidDataH1Pow A₀ ℓg M' q …` (so $B_0$ represents the functor of Weierstrass curves with invertible discriminant equipped with a $\Gamma_0(M')$-kernel tuple, a $\Gamma_1(\ell_g)$-point, a Drinfeld basis of level $q$, and the link condition, modulo variable change), with $B_0$ of finite type over $A_0$. Let $\mathfrak p \subset B_0$ be maximal with $q \in \mathfrak p$, and assume supersingularity at $\mathfrak p$: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : B_0 \to \Omega$ with kernel $\mathfrak p$, the value $\varphi(P_0.j_0)$ of the $j$-invariant of the universal point lies in `ssJSet q Ω`, i.e. every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero $q$-torsion affine point. Put $R_0 =$ `AdicCompletion 𝔭 P₀.B₀`. Then $R_0$ is local, Noetherian, complete for its maximal ideal, with finite residue field of characteristic $q$, and $A_0 \to B_0 \to R_0$ is a tower; there exist a coefficient ring $W_0$, a complete discrete valuation domain with maximal ideal $(q)$, an $A_0$-algebra, with $R_0$ a $W_0$-algebra making $A_0 \to W_0 \to R_0$ a tower via a local homomorphism; a commutative formal group $F$ over $R_0$ and $x_0, x_1 \in R_0$ with `F.IsDrinfeldBasisAdic` for the maximal ideal at $q$ (that is, `F.nthSeries q` is a unit multiple of `F.drinfeldDivisor q x₀ x₁`) and $\mathfrak m_{R_0} = (x_0, x_1)$; elements $T, w \in R_0$ with $w$ a unit and $\operatorname{coeff}_q(F.\mathrm{nthSeries}\ q) - wT \in (q)$; $a_0 \in W_0$, an integer $k \ge 1$, a unit $w' \in R_0$, and a monic $P \in W_0[X]$ of degree $k$ with $P_i \in \mathfrak m_{W_0}^{\lfloor (k-i)q/(q+1)\rfloor + 1}$ for $i < k$, such that: $R_0$ is a regular local ring of Krull dimension $2$; the image of $P_0.j_0$ in $R_0$ minus that of $a_0$ equals $w' \cdot P(T)$; and for every $\gamma \in \Gamma_0(M') \subset \mathrm{SL}_2(\mathbb Z)$ and every automorphism $\rho_\gamma$ of the moduli problem which on points over fields acts by relabelling — whenever $x, x'$ are raw data over an $A_0$-algebra field $T$ with $x$'s Drinfeld-pair curve of invertible discriminant, with the same curve, the same $\Gamma_0(M')$-tuple, with the $\Gamma_1(\ell_g)$-point of $x'$ equal to $\gamma_{00}$ times that of $x$ (via `toPoint`) and with its $Q$-coordinates equal to its $P$-coordinates, and with the Drinfeld pair of $x'$ the relabelling of that of $x$ by the matrix $\gamma$, then $\rho_\gamma$ sends the class of $x$ to the class of $x'$ — and whose induced endomorphism `P₀.classify (ργ.act P₀.univ)` of $B_0$ is the identity modulo $\mathfrak p$, there exist a ring automorphism $\theta_0$ of $R_0$ and $c \in R_0$ such that $\theta_0$ induces that endomorphism on the image of $B_0$, $\theta_0 \equiv \mathrm{id}$ modulo $\mathfrak m_{R_0}$, $\theta_0 x_0 \equiv c(\gamma_{00}x_0 + \gamma_{10}x_1)$ and $\theta_0 x_1 \equiv c(\gamma_{01}x_0 + \gamma_{11}x_1)$ modulo $\mathfrak m_{R_0}^2$, $c^{q+1} \equiv 1$ modulo $\mathfrak m_{R_0}$, $c \equiv 1$ when $\gamma_{11} \equiv 1 \pmod{\ell_g}$, $c \equiv -1$ when $\gamma_{11} \equiv -1 \pmod{\ell_g}$, and $c - 1 \notin \mathfrak m_{R_0}$ whenever $\gamma \in \Gamma(q)$ and $\gamma_{11} \not\equiv 1 \pmod{\ell_g}$ (and, if $q = 2$, also $\gamma_{11} \not\equiv -1 \pmod{\ell_g}$).
--
--   This is the local structure theorem at a supersingular point of the moduli problem with $\Gamma_0(M') \times \Gamma_1(\ell_g) \times$ Drinfeld-$\Gamma(q)$ level structure: the completed local ring is a two-dimensional regular local ring with a Drinfeld basis of the formal group as regular parameters, the universal $j$-invariant is given by a monic Hasse-type polynomial in the Hasse parameter, and the relabelling automorphisms act on the parameters through a scalar multiple of $\bar\gamma$. It is used in the construction of auxiliary level-one data, being cited by [`ModularCurve.FullLevel.AuxLevelOne.exists_ringEquiv_adicCompletion_stalk_regularLocalRing_isDrinfeldBasisAdic_const_hasseParam_monic_levelAut_linearPart_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.exists_ringEquiv_adicCompletion_stalk_regularLocalRing_isDrinfeldBasisAdic_const_hasseParam_monic_levelAut_linearPart_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_problemAut_linearPart_adicCompletion_of_forall_mem_ssJSet_rigidDataH1Pow.lean

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

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance 10000] SubalgebraClass.toAlgebra Algebra.toSMul Algebra.toModule
attribute [local instance 10001] AdicCompletion.instAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_problemAut_linearPart_adicCompletion_of_forall_mem_ssJSet_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)}) [Finite (IsLocalRing.ResidueField A₀)]

    (hℓA : IsUnit ((ℓg : ℕ) : A₀)) (hM'A : IsUnit ((M' : ℕ) : A₀))
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
      (a₀ : W₀) (k : ℕ) (_ : 1 ≤ k) (w' : R₀) (_ : IsUnit w')

      (P : Polynomial W₀) (_ : P.Monic) (_ : P.natDegree = k)
      (_ : ∀ i < k, P.coeff i ∈ IsLocalRing.maximalIdeal W₀ ^ ((k - i) * q / (q + 1) + 1)),
      IsRegularLocalRing R₀ ∧ ringKrullDim R₀ = 2 ∧
      algebraMap P₀.B₀ R₀ P₀.j₀ - algebraMap W₀ R₀ a₀ = w' * (P.map (algebraMap W₀ R₀)).eval T ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ ργ : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.ProblemAut,
          (∀ (T : Type) [Field T] [DecidableEq T] [Algebra A₀ T]
              (x x' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
              x'.curve = x.curve →
              x'.level.1 = x.level.1 →

              ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange T) x'.level.2.1.xP x'.level.2.1.yP =
                (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
                  ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange T) x.level.2.1.xP x.level.2.1.yP →
              x'.level.2.1.xQ = x'.level.2.1.xP → x'.level.2.1.yQ = x'.level.2.1.yP →
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

              (((γ 1 1 : ℤ) : ZMod ℓg) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal R₀) ∧

              (((γ 1 1 : ℤ) : ZMod ℓg) = -1 → c + 1 ∈ IsLocalRing.maximalIdeal R₀) ∧

              (γ ∈ CongruenceSubgroup.Gamma q → ((γ 1 1 : ℤ) : ZMod ℓg) ≠ 1 →
                (q = 2 → ((γ 1 1 : ℤ) : ZMod ℓg) ≠ -1) →
                c - 1 ∉ IsLocalRing.maximalIdeal R₀)) := by sorry
