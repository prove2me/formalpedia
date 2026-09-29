-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_finrank_fractionRing_tensorProduct_quotient_ker_classify_eq_of_dense_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.finrank_fractionRing_tensorProduct_quotient_ker_classify_eq_of_dense_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/814f643c-e553-569f-acc9-1c210efa756b
-- title:
--   Rank of the H₁ classifying quotient at a dense j(mathsf q^q) point
-- statement:
--   Fix a prime $q$, a natural number $M'\ge 1$ with $q\nmid M'$, and a prime $\ell_g$ with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero containing a primitive $(q\ell_g)$-th root of unity $\xi$, together with a ring homomorphism $L\to\mathbb C$ carrying $\xi$ to $\exp(2\pi i/(q\ell_g))$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of reduction to $(\mathbb Z/q)^\times$, with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$, and let $K\subseteq L((\mathsf q))$ be the subfield generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_{H_1}(q^2M')$ over $\mathbb Q$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, with $\ell_g$ and $M'$ units in $A$, and with $K$ an $A$-algebra compatibly; let $j\in K$ have $q$-expansion [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), with $j\neq 0$. Assume the variable-change compatibilities `hℓ`, `hM`, `hL` for the $\Gamma_1(\ell_g)$-point condition, the cyclic-kernel conditions `IsGamma0PowAt` at the prime powers of $M'$, and the divisibility by `inLineMulPoly`; group laws $\mathcal G$ on projective Weierstrass models over $A$-algebras that are chord-tangent and have the origin as identity; a level transport $\mathcal T$ for Drinfeld $\Gamma(q)$-bases satisfying `IsSectionTransport`; and the graded-homomorphism hypotheses `hVC`, `hCO` realising variable changes and coefficient maps on projective models. Let $P_0$ be a fine moduli package, with $B_0$ of finite type over $A$, for the moduli datum `rigidDataH1Pow A ℓg M' q …` of Weierstrass curves with unit discriminant carrying such linked triples of level data up to variable change, let $x$ be a $K$-point of that datum whose $j$-invariant has $q$-expansion [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18), assume $S:=A[P_0.j_0]$ is a domain and that every $k\in K$ is a ratio $\mathrm{classify}_x(a)/\mathrm{classify}_x(b)$ with $\mathrm{classify}_x(b)\neq 0$. Then, with $F$ the fraction field of $S$, $$\dim_F\bigl(F\otimes_S (B_0/\ker \mathrm{classify}_x)\bigr)=\Bigl(\prod_{p\mid M'}p^{v_p(M')-1}(p+1)\Bigr)(\ell_g-1)\,q(q^2-1)/2,$$ the right-hand side computed in $\mathbb N$.
--
--   The right-hand side is $\psi(M')(\ell_g-1)q(q^2-1)/2$, the index of $\pm\Gamma_{H_1}(q^2M')$ in $\mathrm{SL}_2(\mathbb Z)$, so the statement identifies the generic rank over $A[j_0]$ of the component of the fine moduli ring cut out by a $q$-expansion point with $j=j(\mathsf q^q)$ with the degree of $X_{H_1}(q^2M')$ over the $j$-line. It feeds the analysis of the minimal primes of that component and of the Galois action permuting the corresponding kernels, on the way to the Galois-theoretic description of the full-level modular curve used in Diamond-type level arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_finrank_fractionRing_tensorProduct_quotient_ker_classify_eq_of_dense_rigidDataH1Pow.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.finrank_fractionRing_tensorProduct_quotient_ker_classify_eq_of_dense_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L q)
    [IsDomain ↥(Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀))]
    (hdense : ∀ k : ↥K, ∃ a b : P₀.B₀, P₀.classify x b ≠ 0 ∧ k * P₀.classify x b = P₀.classify x a) :
    letI S := ↥(Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀))
    letI F := FractionRing S
    Module.finrank F (TensorProduct S F (P₀.B₀ ⧸ RingHom.ker (P₀.classify x).toRingHom)) =
      (∏ p ∈ M'.primeFactors, p ^ (M'.factorization p - 1) * (p + 1)) *
        (ℓg - 1) * (q * (q ^ 2 - 1)) / 2 := by sorry
