-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_isReduced_residueField_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.isReduced_residueField_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/db9498a7-b4ab-56ca-b0ed-134f17f2f10b
-- title:
--   Reduced special fibre on each component of the H₁ moduli ring
-- statement:
--   Fix a prime $q$, a nonzero $M'$ with $q \nmid M'$, and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Let $L$ be a field of characteristic zero containing a primitive $(q\ell_g)$-th root of unity $\xi$, for which some ring homomorphism $L \to \mathbb{C}$ carries $\xi$ to $\exp(2\pi i/(q\ell_g))$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernels of reduction to $(\mathbb{Z}/q)^\times$ and to $(\mathbb{Z}/\ell_g)^\times$, i.e. the units congruent to $1$ modulo $q$ and modulo $\ell_g$, and let $K \subseteq L(\!(X)\!)$ be the subfield generated over $L$ by the image, under the coefficientwise map from $\mathbb{Q}$-Laurent series, of the $q$-expansion function field of $X_{H_1}$ of level $q^2M'$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, acting on $K$ compatibly, and let $j \in K$ be the element whose Laurent expansion is that of the $j$-invariant, assumed nonzero. Assume $\ell_g$ and $M'$ are units in $A$; assume the three variable-change compatibilities for $\Gamma_1(\ell_g)$-point data, for $\Gamma_0(p^k)$ cyclic-kernel polynomials, and for divisibility of the line-multiplication polynomials; let $\mathcal{G}$ be a family of group laws on projective Weierstrass models over $A$-algebras that is chord-tangent and has the origin as identity, $\mathcal{T}$ a level transport for Drinfeld $q$-bases compatible with sections, and assume graded homomorphisms realising variable changes and coefficient changes exist. Let $P_0$ be a fine moduli package over $A$ for the moduli datum of `rigidDataH1Pow` (curves with invertible discriminant carrying $\Gamma_0(M')$-kernel polynomials, a $\Gamma_1(\ell_g)$-point, a Drinfeld $q$-basis, and the linking divisibility at $\ell_g$, modulo variable change), with $P_0.B_0$ of finite type over $A$. Then for every minimal prime $\mathfrak{p}$ of $P_0.B_0$ the ring $\kappa(A) \otimes_A (P_0.B_0/\mathfrak{p})$ is reduced, where $\kappa(A)$ is the residue field of $A$.
--
--   This is the reducedness of the special fibre at $q$ of each irreducible component of the fine moduli ring for the level structure $H_1$, the classical statement that the fibre at $q$ of the moduli scheme is a union of Igusa-type curves of multiplicity one. It feeds the proof that the components $P_0.B_0/\mathfrak{p}$ are integrally closed, and the corresponding reducedness statement for the chart algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_isReduced_residueField_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow.lean

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

theorem ModularCurve.FullLevel.Diamond.isReduced_residueField_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow
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
    (𝔭 : Ideal P₀.B₀) (h𝔭 : 𝔭 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes) :
    IsReduced (TensorProduct A (IsLocalRing.ResidueField A) (P₀.B₀ ⧸ 𝔭)) := by sorry
