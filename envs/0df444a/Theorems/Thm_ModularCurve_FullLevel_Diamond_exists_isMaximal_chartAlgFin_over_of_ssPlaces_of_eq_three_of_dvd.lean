-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_isMaximal_chartAlgFin_over_of_ssPlaces_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.Diamond.exists_isMaximal_chartAlgFin_over_of_ssPlaces_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/5190c3e6-387f-55b5-a0b2-8295df9d6824
-- title:
--   Maximal ideal of the j-finite chart over a supersingular place, q=3
-- statement:
--   Fix a prime $q$ with $q=3$, a nonzero level $M'$ with $q\nmid M'$, and a prime $\ell_g\equiv 11\pmod{12}$ dividing $M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, and let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular ones (rational, affine geometric, with value of $\mathrm{jGeomGen}$ in $\mathrm{ssJSet}\,q$), with $s\in W$. Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ and let $R_0$ be a constant reduction of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with values in $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$, compatible with coefficientwise reduction: any Laurent series $y$ over $A$ whose image lies in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral, with residue the coefficientwise residue of $y$. Let $k_0\subseteq\overline{\mathbb Q}$ be an intermediate field and $\pi_0\in k_0$ an element of $A$, such that $A_0:=A\cap k_0$ is a henselian discrete valuation ring with maximal ideal $(\pi_0)$ and algebraically closed residue field, and every element of $A$ is congruent modulo the maximal ideal of $A$ to an element of $k_0\cap A$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb Z/q)^\times$ with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$, and $K=\mathrm{laurentBaseChange}\,k_0\,(\mathrm{xHFunctionField}\,(q^2M')\,H_1)$, an intermediate field of $k_0\subseteq \mathrm{LaurentSeries}\,k_0$, equipped with an $A_0$-algebra structure compatible with $k_0$. Let $j\in K$ be nonzero with Laurent expansion $\mathrm{coeffEmb}\,k_0\,\mathrm{jq}$, and assume this expansion lies in $K$ and in $C:=\mathrm{chartAlgFin}\,A_0\,K\,j$, the $A_0$-subalgebra of elements of $K$ integral over $A_0[j]$. Then there is a maximal ideal $y$ of $C$ containing the image of $\pi_0$ and with the following property: for every $g\in\mathrm{modularFunctionFieldFull}\,M'$ whose image in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral, such that $0\le P.\mathrm{ord}$ of that image at every place $P$ of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ at which the image of $\mathrm{jq}$ has nonnegative order, and such that the $R_0$-residue of $g$ lies in the valuation subring of $s$: whenever $\mathrm{coeffEmb}\,k_0\,g$ lies in $K$ and in $C$, and $c\in k_0\cap A$ has residue in $\mathrm{ResidueField}\,A$ equal to the value at $s$ of the $R_0$-residue of $g$, then $g-c$ lies in $y$.
--
--   This produces a point of the closed fibre of the $j$-finite chart of the two-chart integral model of the level-$H_1$ modular curve over the henselian discrete valuation ring $A_0$, specialising the supersingular place $s$ of the level-$M'$ reduction: the point kills $\pi_0$ and matches the values at $s$ of all cusp-regular, $s$-regular modular functions of level $M'$. It is used by the companion statement [`ModularCurve.FullLevel.Diamond.exists_isMaximal_chartAlgFin_mem_ssJSet_over_of_ssPlaces_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.Diamond.exists_isMaximal_chartAlgFin_mem_ssJSet_over_of_ssPlaces_of_eq_three_of_dvd), which adds the supersingularity of the resulting $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_isMaximal_chartAlgFin_over_of_ssPlaces_of_eq_three_of_dvd.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.Diamond.exists_isMaximal_chartAlgFin_over_of_ssPlaces_of_eq_three_of_dvd
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hjK : (coeffEmb ↥k₀ jq) ∈ K)
    (hjC : (⟨_, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) :
    ∃ y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
      y.IsMaximal ∧

      algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨π₀, hπ⟩ ∈ y ∧

      (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        ∀ (hgK : (coeffEmb ↥k₀ g) ∈ K)
          (hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
        ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
          residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
          (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) -
              algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨c, hc⟩ ∈ y) := by sorry
