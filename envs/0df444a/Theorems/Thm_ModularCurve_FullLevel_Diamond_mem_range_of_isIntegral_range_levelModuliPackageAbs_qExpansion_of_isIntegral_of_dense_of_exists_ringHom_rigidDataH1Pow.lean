-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_mem_range_of_isIntegral_range_levelModuliPackageAbs_qExpansion_of_isIntegral_of_dense_of_exists_ringHom_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.mem_range_of_isIntegral_range_levelModuliPackageAbs_qExpansion_of_isIntegral_of_dense_of_exists_ringHom_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/d6c59ee3-337d-5e64-b3cd-70ba4321073f
-- title:
--   Integral closedness of the q-expansion image, Γ₁(ℓ_g) edition
-- statement:
--   Let $q$ be a prime and $M'\ge 1$ with $q\nmid M'$, and let $\ell_g$ be a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero containing a primitive $q\ell_g$-th root of unity $\xi$, together with a ring homomorphism $L\to\mathbb C$ carrying $\xi$ to $\exp(2\pi i/(q\ell_g))$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb Z/q)^\times$ with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$, and let $K\subseteq L(\!(\mathsf q)\!)$ be the intermediate field generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_{H_1}(q^2M')$. Let $A$ be a discrete valuation domain with fraction field $L$ and $q$ in its maximal ideal, with $K$ an $A$-algebra compatibly with $L$, and let $j\in K$ be nonzero with Laurent expansion the image of the $q$-expansion of $j$. Assume $\ell_g$ and $M'$ are units in $A$; assume the three equivariance hypotheses that $\Gamma_1(\ell_g)$-points, $\Gamma_0(p^k)$-kernel polynomials and the $\Gamma_1$-divisibility link are preserved by Weierstrass variable changes; fix group laws $\mathcal G$ on projective Weierstrass curves over $A$-algebras which are chord–tangent and have the origin as identity, and a level transport $\mathcal T$ for $q$-Drinfeld bases which is a section transport; assume further that variable changes and coefficient changes of projective models are realised by graded ring homomorphisms respecting the irrelevant ideals. Let $P_0$ be an abstract package, of finite type over $A$, representing the level moduli datum of the guarded $H_1$-data $\mathtt{rigidDataH1Pow}$, with coordinate ring $B_0$ and universal $j$-invariant $j_0$, and let $\iota:B_0\to K$ be an $A$-algebra map such that $\iota(j_0)$ is integral over $A[j]$, $j$ is integral over $A[\iota(j_0)]$, and every element of $K$ is a quotient $\iota(x)/\iota(y)$ with $\iota(y)\neq 0$. Then every $x\in K$ integral over the image of $\iota$ already lies in that image.
--
--   This is the normality statement for the image of the fine moduli ring inside the $q$-expansion function field, in the version where the auxiliary rigidification is a $\Gamma_1(\ell_g)$-point at a guard prime $\ell_g\equiv 11\pmod{12}$ dividing $M'$, valid for every prime $q\nmid M'$. It is used to identify the range of the classifying map with the chart algebra at full level, a step in setting up the integral models of modular curves employed in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_mem_range_of_isIntegral_range_levelModuliPackageAbs_qExpansion_of_isIntegral_of_dense_of_exists_ringHom_rigidDataH1Pow.lean

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

theorem ModularCurve.FullLevel.Diamond.mem_range_of_isIntegral_range_levelModuliPackageAbs_qExpansion_of_isIntegral_of_dense_of_exists_ringHom_rigidDataH1Pow
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
    (ι : P₀.B₀ →ₐ[A] ↥K)
    (hι : IsIntegral ↥(Algebra.adjoin A ({j} : Set ↥K)) (ι P₀.j₀))
    (hι' : IsIntegral ↥(Algebra.adjoin A ({ι P₀.j₀} : Set ↥K)) j)
    (hdense : ∀ k : ↥K, ∃ x y : P₀.B₀, ι y ≠ 0 ∧ k * ι y = ι x) :
    ∀ x : ↥K, IsIntegral ↥ι.range x → x ∈ ι.range := by sorry
