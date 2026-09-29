-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_isMaximal_chartAlgFin_comap_eq_of_coeffMap_cyclotomic_rigidDataPow
-- name    : ModularCurve.FullLevel.exists_isMaximal_chartAlgFin_comap_eq_of_coeffMap_cyclotomic_rigidDataPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/14a50366-1c11-5e60-98ad-816d1c5b97ff
-- title:
--   Supersingular closed point lifts to the chart over admissible constants
-- statement:
--   Fix a prime $q\ge 5$ and $M'\neq 0$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. The first block of hypotheses concerns the reduction of constants: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ consisting exactly of the supersingular places $\mathrm{ssPlaces}\,q\,M'$, the inclusion $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, and a `ConstantReduction` $R_0$ of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with values in $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A,M')$ whose residue map, on any Laurent series with coefficients in $A$ lying in $\mathrm{modularFunctionFieldBar}\,M'$, is coefficientwise reduction modulo the maximal ideal of $A$. Next, an intermediate field $k_0$ of $\overline{\mathbb Q}/\mathbb Q$ and $\pi_0\in k_0$ with $\pi_0\in A$ are given such that $A_0:=A\cap k_0$ is a Henselian discrete valuation ring with maximal ideal $(\pi_0)$ and algebraically closed residue field, and such that every element of $A$ is congruent modulo the maximal ideal of $A$ to an element of $k_0\cap A$. Further, a prime $\ell'\neq q$ with $\ell'\ge 3$ and $\ell'\nmid M'$, a primitive $(q\ell')$-th root of unity $\xi\in k_0$ admitting a ring embedding of $k_0$ into $\mathbb C$ carrying $\xi$ to $e^{2\pi i/(q\ell')}$, the field $K$ obtained from the $X_H$ function field of level $((q\ell')^2M', \mathrm{levelH}(q\ell')\,M')$ by base change to $k_0$ inside $\mathrm{LaurentSeries}\,k_0$ with compatible $A_0$-algebra structure, and a non-zero $j\in K$ whose Laurent expansion is the coefficientwise image of $\mathrm{jq}$. A package of functoriality data over $A_0$-algebras is assumed, summarised here: compatibility of $\mathrm{IsLevelPStructure}$ at $\ell'$ and of $\mathrm{IsGamma0PowAt}$ with Weierstrass variable changes, group laws $\mathcal G$ which are chord-tangent with origin as identity, a level transport $\mathcal T$ at $q$ which is a section transport, and the existence of graded ring maps on the projective-model graded rings realising variable changes and coefficient maps, with the stated inequality on irrelevant ideals. Finally the cyclotomic frame: a characteristic-zero field $L_1$ which is a cyclotomic extension of $\mathbb Q$ for $\{q\ell'\}$, primitive roots of unity $\zeta_1$ of order $q$ and $\xi_1$ of order $q\ell'$ in $L_1$, the analogous field $K_1$ over $L_1$, a discrete valuation ring $A_1$ with fraction field $L_1$ such that $q$ lies in its maximal ideal and $\zeta_1$ comes from $A_1$, a non-zero $j_1\in K_1$ with Laurent expansion the coefficientwise image of $\mathrm{jq}$, a uniformiser $\varpi_1$ of $A_1$, a point $z_1$ of $\mathrm{TwoChartIntegralModel}\,A_1\,K_1\,j_1$ at which the germ of the global section coming from $\varpi_1$ lies in the maximal ideal of the stalk, a point $y_1$ of $\mathrm{XFin}=\mathrm{Spec}$ of $\mathrm{chartAlgFin}\,A_1\,K_1\,j_1$ mapping to $z_1$, such that every ring map from $\mathrm{chartAlgFin}\,A_1\,K_1\,j_1$ to an algebraically closed field of characteristic $q$ with kernel $y_1$ sends $\mathrm{jChartFin}$ into $\mathrm{ssJSet}\,q$, that is, to a value $j$ for which every elliptic curve with that $j$-invariant has no non-zero $q$-torsion point. Lastly a ring homomorphism $\iota\colon L_1\to k_0$ with $\iota\xi_1=\xi$, carrying $A_1$ into $A$ and with $\iota^{-1}(A)$ contained in the image of $A_1$, and a ring homomorphism $c$ from $\mathrm{chartAlgFin}\,A_1\,K_1\,j_1$ to $\mathrm{chartAlgFin}\,A_0\,K\,j$ which on Laurent expansions is coefficientwise application of $\iota$. The conclusion: there is a maximal ideal $y'$ of $\mathrm{chartAlgFin}\,A_0\,K\,j$ containing the image of $\pi_0$ under the structure map and satisfying $c^{-1}(y')=y_1$.
--
--   This is the descent-of-base step for the $j$-finite chart of the two-chart integral model: a closed point of the special fibre of the chart over the cyclotomic discrete valuation ring $A_1$ is transferred, along the coefficientwise map induced by $\iota\colon L_1\to k_0$, to a closed point of the special fibre of the chart over the ring $A_0=A\cap k_0$ of admissible constants. It is used by [`ModularCurve.FullLevel.exists_ringHom_chartAlgFin_levelAut_comap_eq_of_isLevelAutAt_of_ringHom_cyclotomic_rigidDataPow`](thm.html#ModularCurve.FullLevel.exists_ringHom_chartAlgFin_levelAut_comap_eq_of_isLevelAutAt_of_ringHom_cyclotomic_rigidDataPow), where the supersingular point so obtained is the source of the required specialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_isMaximal_chartAlgFin_comap_eq_of_coeffMap_cyclotomic_rigidDataPow.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry
open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_isMaximal_chartAlgFin_comap_eq_of_coeffMap_cyclotomic_rigidDataPow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'q : ℓ' ≠ q) (hℓ'3 : 3 ≤ ℓ') (hℓ'M' : ¬ ℓ' ∣ M')
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ' D →
        ModularCurve.IsLevelPStructure (C • W) ℓ' (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] [CommRing T'] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T'] (f : T →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)

    (L₁ : Type) [Field L₁] [CharZero L₁] [IsCyclotomicExtension {q * ℓ'} ℚ L₁]
    (ζ₁ : L₁) (hζ₁ : IsPrimitiveRoot ζ₁ q)
    (ξ₁ : L₁) (hξ₁ : IsPrimitiveRoot ξ₁ (q * ℓ'))
    (K₁ : IntermediateField L₁ (LaurentSeries L₁))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L₁
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁] [Algebra A₁ L₁] [IsFractionRing A₁ L₁]
    (hA₁q : (q : A₁) ∈ IsLocalRing.maximalIdeal A₁) (hζA₁ : ∃ x : A₁, algebraMap A₁ L₁ x = ζ₁)
    [Algebra A₁ ↥K₁] [IsScalarTower A₁ L₁ ↥K₁]
    (j₁ : ↥K₁) (hj₁ : ((j₁ : LaurentSeries L₁)) = ModularCurve.coeffEmb L₁ ModularCurve.jq) [Fact (j₁ ≠ 0)]
    (ϖ₁ : A₁) (hϖ₁ : IsLocalRing.maximalIdeal A₁ = Ideal.span {ϖ₁})
    (z₁ : ↥(AlgebraicCurve.TwoChartIntegralModel A₁ (↥K₁) j₁))
    (ϖz₁ : (AlgebraicCurve.TwoChartIntegralModel A₁ (↥K₁) j₁).presheaf.stalk z₁)
    (hϖz₁ : ϖz₁ = ((AlgebraicCurve.TwoChartIntegralModel A₁ (↥K₁) j₁).presheaf.germ ⊤ z₁ trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A₁ (↥K₁) j₁).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁)))
    (hz₁ : ϖz₁ ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₁ (↥K₁) j₁).presheaf.stalk z₁))
    (y₁ : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₁ (↥K₁) j₁))
    (hy₁ : (AlgebraicCurve.TwoChartIntegralModel.ιFin A₁ (↥K₁) j₁).base y₁ = z₁)
    (hss₁ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁) →+* Ω),
      RingHom.ker φ = y₁.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₁ (↥K₁) j₁) ∈ ModularCurve.ssJSet q Ω)

    (ι : L₁ →+* ↥k₀) (hιξ₁ : ι ξ₁ = ξ)
    (hιA : ∀ a : A₁, ((ι (algebraMap A₁ L₁ a) : ↥k₀) : AlgebraicClosure ℚ) ∈ A)
    (hιA' : ∀ x : L₁, ((ι x : ↥k₀) : AlgebraicClosure ℚ) ∈ A → ∃ a : A₁, algebraMap A₁ L₁ a = x)

    (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))
    (hc : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁), (((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) : LaurentSeries ↥k₀) =
      ModularCurve.coeffMap ι (((a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁)) : ↥K₁) : LaurentSeries L₁)) :
    ∃ y' : {y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) // y.IsMaximal ∧ algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨π₀, hπ⟩ ∈ y}, Ideal.comap c y'.1 = y₁.asIdeal := by sorry
