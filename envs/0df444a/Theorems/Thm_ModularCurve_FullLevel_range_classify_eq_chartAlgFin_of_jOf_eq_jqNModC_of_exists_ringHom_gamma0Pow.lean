-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_range_classify_eq_chartAlgFin_of_jOf_eq_jqNModC_of_exists_ringHom_gamma0Pow
-- name    : ModularCurve.FullLevel.range_classify_eq_chartAlgFin_of_jOf_eq_jqNModC_of_exists_ringHom_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/3dfe0a83-93d0-5101-9d98-cbdaffa4602a
-- title:
--   Classifying map's image is the integral closure of A[j]
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\neq q$, and let $M'\neq 0$ be a natural number divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic zero containing a primitive $q\ell$-th root of unity $\xi$ for which some ring homomorphism $\iota:L\to\mathbb C$ satisfies $\iota\xi=\exp(2\pi i/(q\ell))$, and let $K$ be the intermediate field of $L\subset\mathrm{LaurentSeries}\,L$ obtained as `laurentBaseChange`, i.e. generated over $L$ by the coefficientwise image of the $q$-expansion function field `xHFunctionField` of level $(q\ell)^2M'$ for the subgroup `levelH`, the kernel of the reduction $(\mathbb Z/(q\ell)^2M')^\times\to(\mathbb Z/q\ell)^\times$. Let $A$ be a discrete valuation domain with fraction field $L$ and $q$ in its maximal ideal, with $K$ an $A$-algebra compatibly with $A\to L\to K$, and let $j\in K$ be nonzero with image $\mathrm{coeffEmb}_L(\mathrm{jq})$ in $\mathrm{LaurentSeries}\,L$. Assume $\ell$ and $M'$ are units in $A$; that level-$\ell$ structures (`IsLevelPStructure`) and the $\Gamma_0(p^k)$-kernel conditions (`IsGamma0PowAt`) are preserved under Weierstrass variable changes, in the latter case via `kernelVariableChangeDeg`; that graded homomorphisms of projective-model rings realising variable changes and coefficient maps exist, respecting irrelevant ideals (`hVC`, `hCO`); and fix group laws $\mathcal G$ over $A$ that are chord–tangent and origin-normalised, together with a Drinfeld level transport $\mathcal T$ for $q$ satisfying the section-transport condition. Let $P_0$ be a package representing the moduli datum of $\mathrm{rigidDataPow}(A,\ell,M',q,\dots)$ — Weierstrass curves with unit discriminant carrying a $\Gamma_0(p^k)$-tuple for the prime powers of $M'$, a level-$\ell$ structure and a Drinfeld $q$-basis, modulo variable change — with $B_0$ of finite type over $A$. Then for every $K$-point $x$ of this moduli problem whose $j$-invariant, read in $\mathrm{LaurentSeries}\,L$, equals $\mathrm{jqNModC}_L(q\ell)$, the range of the classifying $A$-algebra map $P_0.\mathrm{classify}\,x:B_0\to K$ equals $\mathrm{chartAlgFin}\,A\,K\,j$, the subalgebra of elements of $K$ integral over $A[j]$.
--
--   This identifies the image of the fine moduli ring of the full-level problem in the function field $K$ with the finite chart of the two-chart integral model of the modular curve, in the style of the moduli-theoretic description of affine modular curves of Katz–Mazur and Deligne–Rapoport. It feeds the subsequent analysis of that chart (automorphisms acting on it, reducedness of its residue-field base changes, and the identification of its maximal ideals with $j$-values).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_range_classify_eq_chartAlgFin_of_jOf_eq_jqNModC_of_exists_ringHom_gamma0Pow.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.range_classify_eq_chartAlgFin_of_jOf_eq_jqNModC_of_exists_ringHom_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
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
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀] :
    ∀ (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K),
      (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * ℓ) →
      (P₀.classify x).range = AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := by sorry
