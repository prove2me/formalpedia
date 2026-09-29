-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_adicCompletion_of_forall_mem_ssJSet_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_adicCompletion_of_forall_mem_ssJSet_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/e4b12a18-36a8-5dfc-b41c-7e6747ac2ec2
-- title:
--   Regular two-dimensional complete local ring at a supersingular point
-- statement:
--   Fix primes $q \ge 5$ and $\ell \ge 3$ with $\ell \neq q$, and a non-zero natural number $M'$ with $q \nmid M'$. Let $A_0$ be a discrete valuation ring (a domain) whose maximal ideal is $(q)$ and whose residue field is finite, and in which the images of $\ell$ and of $M'$ are units. Assume: $(hℓ)$ for every $A_0$-algebra $T$, level-$\ell$ data $D = (x_P,y_P,x_Q,y_Q)$ satisfying `IsLevelPStructure W ℓ D` (both points lie on the affine Weierstrass equation of $W$, $(W.\mathrm{preΨ}\,\ell)$ vanishes at $x_P$ and at $x_Q$, and `indepElt W ℓ` is a unit in both orders) transform under a variable change $C$ to data satisfying `IsLevelPStructure (C • W) ℓ (D.variableChange C)`; $(hM)$ the predicate `IsGamma0PowAt W p k h` (a two-torsion kernel condition when $p^k = 2$, and otherwise: $\deg h \le \varphi(p^k)/2$ with that coefficient $1$, $h \cdot W.\mathrm{preΨ}(p^{k-1}) \mid W.\mathrm{preΨ}(p^{k})$, and the stated divisibilities of the multiplication numerators) is preserved under variable change, with $h$ replaced by `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; a family $\mathcal G$ of relative group laws on the projective models of Weierstrass curves with invertible discriminant over $A_0$-algebras which is chord–tangent and has the unit section as the origin of the origin chart; a level transport $\mathcal T$ for raw Drinfeld pairs satisfying `IsSectionTransport`; and $(hVC)$, $(hCO)$ the existence, for every variable change and every $A_0$-algebra map, of graded ring homomorphisms between the graded projective-model rings realising the variable change, respectively the coefficient change, and carrying the irrelevant ideal appropriately. Let $P_0$ be a fine moduli package (a ring $B_0$ with a universal point and unique classifying maps) for the moduli datum $D$ attached to `rigidDataPow A₀ ℓ M' q`, namely Weierstrass curves with invertible discriminant equipped with a $\Gamma_0$-type kernel polynomial for each prime power dividing $M'$, a level-$\ell$ structure, and a Drinfeld level-$q$ pair, taken up to variable change; assume $B_0$ is of finite type over $A_0$. Let $\mathfrak p \subset B_0$ be a maximal ideal containing the image of $q$ such that every ring homomorphism $\varphi : B_0 \to \Omega$ into an algebraically closed field of characteristic $q$ with kernel $\mathfrak p$ satisfies $\varphi(j_0) \in$ `ssJSet q Ω`, i.e. every elliptic curve over $\Omega$ with that $j$-invariant has no non-zero $q$-torsion point; here $j_0 \in B_0$ is the universal $j$-invariant. Then, for $R_0 :=$ `AdicCompletion 𝔭 B₀`, the ring $R_0$ is local, noetherian, complete for its maximal-ideal topology, with finite residue field of characteristic $q$; there is a complete discrete valuation ring $W_0$ (a domain) with maximal ideal $(q)$, an $A_0$-algebra, with a local algebra map $W_0 \to R_0$ compatible with $A_0$, and the scalar tower $A_0 \to B_0 \to R_0$; there are a commutative formal group $F$ over $R_0$ and $x_0, x_1 \in R_0$ such that `F.nthSeries q` is a unit multiple of `F.drinfeldDivisor q x₀ x₁` for the $\mathfrak m_{R_0}$-adic structure, and $\mathfrak m_{R_0} = (x_0, x_1)$; there are $T, w \in R_0$ with $w$ a unit and $\mathrm{coeff}_q(F.\mathrm{nthSeries}\,q) - wT \in (q)$; and there are $a_0 \in W_0$, $k \ge 1$ and a unit $w' \in R_0$ such that $R_0$ is a regular local ring of Krull dimension $2$ and $j_0 - a_0 = w' T^{k}$ in $R_0$.
--
--   This is the moduli-theoretic local structure of the modular curve with $\Gamma_0(M')$, full level $\ell$ and Drinfeld level $q$ data at a supersingular point in characteristic $q$ over an unramified base: the completed local ring is the universal deformation ring of a formal group of height two with a Drinfeld basis, regular of dimension two with the basis as a regular system of parameters, and the universal $j$-invariant differs from a constant by a unit times a power of the Hasse parameter. It is used to compute the completed stalks of the full-level moduli scheme at supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_adicCompletion_of_forall_mem_ssJSet_gamma0Pow.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_isDrinfeldBasisAdic_isRegularLocalRing_hasseParam_adicCompletion_of_forall_mem_ssJSet_gamma0Pow
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
      algebraMap P₀.B₀ R₀ P₀.j₀ - algebraMap W₀ R₀ a₀ = w' * T ^ k := by sorry
