-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isPrime_comap_drinfeldChart_eq_of_isPrime_le_ne_twoChartIntegralModel
-- name    : ModularCurve.FullLevel.AuxLevel.exists_isPrime_comap_drinfeldChart_eq_of_isPrime_le_ne_twoChartIntegralModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/3559aeed-84d2-5ef0-beac-e8e12dbabcb1
-- title:
--   Primes of the j-finite chart lift to the Drinfeld chart
-- statement:
--   Fix a prime $q \ge 5$, an integer $M' \ne 0$ with $q \nmid M'$, and a prime $\ell \ge 3$ with $\ell \ne q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta \in L$ be a primitive $q$-th root of unity and $\xi \in L$ a primitive $q\ell$-th root of unity, and let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image, under the coefficientwise map $\mathrm{LaurentSeries}\,\mathbb{Q} \to \mathrm{LaurentSeries}\,L$, of the $q$-expansion function field `xHFunctionField` at level $(q\ell)^2 M'$ for the subgroup `levelH` of $(\mathbb{Z}/(q\ell)^2M')^\times$ consisting of the units congruent to $1$ modulo $q\ell$ (the kernel of reduction to $(\mathbb{Z}/q\ell)^\times$). Let $A$ be a discrete valuation ring with fraction field $L$ such that $q$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $A \subseteq L \subseteq K$, and let $j \in K$ be nonzero with underlying Laurent series the image of $\mathrm{jq} = T^{-1}\cdot \mathrm{jNumQ}$ under the coefficient embedding; let $\varpi$ generate the maximal ideal of $A$. Let $\mathfrak{X} = \mathrm{TwoChartIntegralModel}\,A\,K\,j$, the pushout of the two affine charts $\operatorname{Spec}$ of the integral closures $C =$ `chartAlgFin` of $A[j]$ and of `chartAlgInf` of $A[j^{-1}]$ in $K$, and let $z$ be a point of $\mathfrak{X}$ such that the germ at $z$ of the image of $\varpi$ under the structure morphism $\mathfrak{X} \to \operatorname{Spec} A$ lies in the maximal ideal of the stalk $\mathcal{O}_{\mathfrak{X},z}$. Let $y$ be a point of $\operatorname{Spec} C$ mapping to $z$ under the chart immersion, and assume that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi \colon C \to \Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in `ssJSet` $q\,\Omega$, i.e. every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$. Let $W$ be a complete discrete valuation ring and $\sigma \colon A \to W$ a ring homomorphism with $\sigma\varpi$ generating the maximal ideal of $W$; let $u, v \in W[[X_0,X_1]]$ be units and $f \in W[[X_0,X_1]]$ with $f - (X_0X_1^q - X_0^qX_1) \in (X_0,X_1)^{q+2}$, and let $e$ be a ring isomorphism from the adic completion of $\mathcal{O}_{\mathfrak{X},z}$ at its maximal ideal onto $S = W[[X_0,X_1]]/(C(\sigma\varpi)\,v - f\,u)$ carrying, for each $a \in A$, the image in the completion of the germ at $z$ of $a$ to the class of the constant series $C(\sigma a)$. Then for every prime $\mathfrak{p}$ of $C$ containing the image of $\varpi$ and satisfying $\mathfrak{p} \subsetneq y$, there is a prime $P'$ of $S$ containing the class of $C(\sigma\varpi)$, with the class of $X_0$ or the class of $X_1$ outside $P'$, whose contraction along the composite of the canonical map $C \to \mathcal{O}_{\mathfrak{X},z}$ (the germ at $z$ over the image of the finite chart), the completion map $\mathcal{O}_{\mathfrak{X},z} \to \widehat{\mathcal{O}}_{\mathfrak{X},z}$ and $e$ equals $\mathfrak{p}$.
--
--   A going-down statement for the flat composite $C \to \mathcal{O}_{\mathfrak{X},z} \to \widehat{\mathcal{O}}_{\mathfrak{X},z} \cong S$: each prime of the $j$-finite chart strictly below the supersingular point $y$, containing the uniformiser, is the contraction of a prime of the Drinfeld local chart other than its maximal ideal. It is used in the analysis of the components of the special fibre through the supersingular point via the equation $\sigma\varpi\,v = f\,u$ with $f$ congruent to the Drinfeld form $X_0X_1^q - X_0^qX_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_isPrime_comap_drinfeldChart_eq_of_isPrime_le_ne_twoChartIntegralModel.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.exists_isPrime_comap_drinfeldChart_eq_of_isPrime_le_ne_twoChartIntegralModel
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (σ : A →+* W)
      (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
      (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
    (hconst :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))))
    (𝔭 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (h𝔭 : 𝔭.IsPrime)
    (hϖ𝔭 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ 𝔭) (h𝔭y : 𝔭 ≤ y.asIdeal) (h𝔭ne : 𝔭 ≠ y.asIdeal) :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
      ∃ P' : Ideal S, P'.IsPrime ∧ (mkS (MvPowerSeries.X 0) ∉ P' ∨ mkS (MvPowerSeries.X 1) ∉ P') ∧
        mkS (MvPowerSeries.C (σ ϖ)) ∈ P' ∧
        Ideal.comap ((e : CMP →+* S).comp (toC.comp germY)) P' = 𝔭 := by sorry
