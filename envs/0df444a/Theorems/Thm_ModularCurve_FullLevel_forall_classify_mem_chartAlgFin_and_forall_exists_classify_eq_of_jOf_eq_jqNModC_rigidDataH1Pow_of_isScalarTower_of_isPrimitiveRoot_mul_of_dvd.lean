-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_classify_mem_chartAlgFin_and_forall_exists_classify_eq_of_jOf_eq_jqNModC_rigidDataH1Pow_of_isScalarTower_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.forall_classify_mem_chartAlgFin_and_forall_exists_classify_eq_of_jOf_eq_jqNModC_rigidDataH1Pow_of_isScalarTower_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/d04b0411-e70e-582f-b57d-7e324343352f
-- title:
--   Classifying map image equals the j-integral chart algebra
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic $0$ containing a primitive $(q\ell)$-th root of unity $\xi$ such that some ring homomorphism $L \to \mathbb{C}$ sends $\xi$ to $e^{2\pi i/(q\ell)}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ with the kernel of reduction to $(\mathbb{Z}/\ell)^\times$, and let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image of the function field of $X_{H_1}$ of level $q^2M'$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, acting on $K$ compatibly, and let $j \in K$, $j \neq 0$, have image in $\mathrm{LaurentSeries}\,L$ the $q$-expansion $\mathtt{jq}$ of the modular $j$-invariant with coefficients in $L$. Let $A_0$ be a discrete valuation domain with maximal ideal $(q)$, containing a primitive $\ell$-th root of unity, with $\ell$ and $M'$ units in $A_0$, mapping to $A$ and to $K$ compatibly. Assume the variable-change compatibilities `hℓ`, `hM`, `hL` of the $\Gamma_1(\ell)$-point condition, of the prime-power $\Gamma_0$ kernel-polynomial condition `IsGamma0PowAt`, and of divisibility of `inLineMulPoly`; group laws $\mathcal{G}$ over $A_0$ that are chord-tangent and origin-normalised, a level transport $\mathcal{T}$ for $q$ that is a section transport, and the graded realisations `hVC`, `hCO` of variable changes and of coefficient maps on projective-model graded rings. Finally let $P_0$ be a fine moduli package over $A_0$ for the level moduli datum attached to `rigidDataH1Pow A₀ ℓ M' q hℓ hM hL 𝒢 𝒯`, with $P_0.B_0$ of finite type over $A_0$. Then for every $K$-point $x$ of that datum whose $j$-invariant has image $\mathtt{jqNModC}\,L\,q$ in $\mathrm{LaurentSeries}\,L$, and such that every element of $A$ lies in the image of the classifying homomorphism $P_0.B_0 \to K$ of $x$, that image is contained in `chartAlgFin A K j`, the subalgebra of elements of $K$ integral over $A[j]$, and conversely every element of that subalgebra is a value of the classifying homomorphism; that is, the image is exactly the chart algebra.
--
--   This identifies the image of the fine moduli ring of the rigidified $\Gamma_0(M')$–$\Gamma_1(\ell)$–Drinfeld-$q$-level problem, evaluated at the point with $j$-invariant the $q$-expansion $j(\mathfrak q^q)$, with the affine chart algebra of elements integral over $A[j]$, in the auxiliary $\Gamma_1(\ell)$ frame with $\ell \equiv 11 \pmod{12}$ that permits small $q$. It supplies the membership and surjectivity inputs for the subsequent comparison of completed local rings with stalks of the two-chart integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_classify_mem_chartAlgFin_and_forall_exists_classify_eq_of_jOf_eq_jqNModC_rigidDataH1Pow_of_isScalarTower_of_isPrimitiveRoot_mul_of_dvd.lean

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
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.forall_classify_mem_chartAlgFin_and_forall_exists_classify_eq_of_jOf_eq_jqNModC_rigidDataH1Pow_of_isScalarTower_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)}) [Algebra A₀ ↥K]
    (hω : ∃ ω : A₀, IsPrimitiveRoot ω ℓ)

    [Algebra A₀ A] [IsScalarTower A₀ A ↥K]

    (hℓA : IsUnit ((ℓ : ℕ) : A₀)) (hM'A : IsUnit ((M' : ℕ) : A₀))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓ M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A₀ P₀.B₀] :
    ∀ (x : (rigidDataH1Pow A₀ ℓ M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K),
      (((rigidDataH1Pow A₀ ℓ M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L q →

      (∀ a : A, ∃ b : P₀.B₀, P₀.classify x b = algebraMap A ↥K a) →
      (∀ b : P₀.B₀, P₀.classify x b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ∧
      (∀ c : ↥K, c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j → ∃ b : P₀.B₀, P₀.classify x b = c) := by sorry
