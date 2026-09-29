-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_residue_pow_eq_evalAt_of_jqNModC_sub_mem_of_over
-- name    : ModularCurve.FullLevel.residue_pow_eq_evalAt_of_jqNModC_sub_mem_of_over
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/5dfed704-4c60-5957-b174-fcd267a8d783
-- title:
--   Frobenius pinning at a supersingular place
-- statement:
--   Let $q\ge 5$ be a prime and $M'\ge 1$ with $q\nmid M'$; let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a non-unit (`LiesOverPrime`), with residue field $\kappa=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'=\kappa\bigl(j(\mathsf q),j(\mathsf q^{M'})\bigr)$ over $\kappa$ whose members are exactly the supersingular places, i.e. the rational affine geometric places $w$ with $w.\mathrm{evalAt}$ of the geometric $j$-generator lying in $\mathrm{ssJSet}\,q\,\kappa$, and let $s\in W$. Let $R_0$ be a constant reduction at $A$ of $\mathrm{modularFunctionFieldBar}\,M'$, the field generated over $\overline{\mathbb Q}$ inside $\overline{\mathbb Q}((\mathsf q))$ by the coefficientwise images of the $\mathsf q$-expansions $j(\mathsf q^{d})$, $d\mid M'$, with values in the above field over $\kappa$; it is assumed (`hR₀`) to be coefficientwise: every Laurent series with coefficients in $A$ that lies in this field is $R_0$-integral and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction. Let $k_0\subseteq\overline{\mathbb Q}$ be an intermediate field and $\pi_0\in k_0$ with $\pi_0\in A$, such that $A_0:=A\cap k_0$ (the comap of $A$ along $k_0\to\overline{\mathbb Q}$) is a discrete valuation ring with maximal ideal $(\pi_0)$. Let $\ell'\ge 3$ be a prime with $\ell'\ne q$ and $\ell'\nmid M'$, and let $K_\ell\subseteq k_0((\mathsf q))$ be the field obtained by adjoining to $k_0$ the coefficientwise images of the $\mathsf q$-expansion function field of $X_H$ of level $(q\ell')^2M'$, $H$ the kernel of the reduction $(\mathbb Z/(q\ell')^2M')^\times\to(\mathbb Z/q\ell')^\times$ (units $\equiv 1\bmod q\ell'$), made an $A_0$-algebra compatibly with $k_0$. Let $j_\ell\in K_\ell$ be nonzero with Laurent series the coefficientwise image of $j(\mathsf q)$, let $C=\mathrm{chartAlgFin}\,A_0\,K_\ell\,j_\ell$ be the $A_0$-subalgebra of elements of $K_\ell$ integral over $A_0[j_\ell]$, and let $y\subset C$ be a maximal ideal containing the image of $\pi_0$. Assume the hypothesis `hover`: for every $g$ in the level-$M'$ full modular function field over $\mathbb Q$ whose base change to $\overline{\mathbb Q}$ is $R_0$-integral, such that $\mathrm{ord}_P(g)\ge 0$ at every place $P$ of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ at which $\mathrm{ord}_P(j(\mathsf q))\ge 0$, and such that the $R_0$-residue of $g$ lies in the valuation ring of $s$, whenever $\mathrm{qExpand}\,k_0\,\ell'$ of the coefficientwise image of $g$ lies in $K_\ell$ and in $C$, and $c\in k_0$ lies in $A$ with residue in $\kappa$ equal to $s.\mathrm{evalAt}$ of the $R_0$-residue of $g$, one has $g(\mathsf q^{\ell'})-c\in y$. Finally assume $j(\mathsf q^{q\ell'})=\mathrm{jqNModC}\,k_0\,(q\ell')$ lies in $K_\ell$ and in $C$, and that $a_0\in A_0$ satisfies $j(\mathsf q^{q\ell'})-a_0\in y$. Then, granting that the base change of $j(\mathsf q)$ is $R_0$-integral and that $a_0$ lies in $A$, the residue of $a_0$ in $\kappa$ satisfies $$\bigl(\mathrm{residue}_A(a_0)\bigr)^{q}=s.\mathrm{evalAt}\bigl(R_0\text{-residue of }j(\mathsf q)\bigr),$$ where $s.\mathrm{evalAt}$ of an element of the valuation ring of $s$ is its residue pulled back to $\kappa$ along $\kappa\to$ the residue field of $s$ (and $0$ for elements outside that valuation ring).
--
--   This is the Frobenius-pinning step: Kronecker's congruence $\Phi_q(X,Y)\equiv(X^q-Y)(X-Y^q)\bmod q$ applied to the pair $j(\mathsf q^{q\ell'}),\,j(\mathsf q^{\ell'})$ on the chart $C$, combined with the fact that the supersingular value $\hat\jmath(s)$ satisfies $x^{q^2}=x$, identifies the reduction of $a_0$ at $y$ with a $q$-th root of $\hat\jmath(s)$. It feeds the construction of the rigid local data at the Tate point in [`ModularCurve.FullLevel.forall_nsmul_eq_zero_and_exists_variableChange_of_over_of_eq_map_classify_rigidDataPow_of_tatePoint`](thm.html#ModularCurve.FullLevel.forall_nsmul_eq_zero_and_exists_variableChange_of_over_of_eq_map_classify_rigidDataPow_of_tatePoint).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_residue_pow_eq_evalAt_of_jqNModC_sub_mem_of_over.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 12800000

open AlgebraicCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open ModularCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.residue_pow_eq_evalAt_of_jqNModC_sub_mem_of_over
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
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
    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'3 : 3 ≤ ℓ') (hℓ'q : ℓ' ≠ q) (hℓ'M : ¬ ℓ' ∣ M')
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)]
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y)

    (hover :
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
      ∀ (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ)
        (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
      ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
        (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
            algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y))
    (hjK : ModularCurve.jqNModC ↥k₀ (q * ℓ') ∈ Kℓ)
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y)
    :
    ∀ (hjR : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
      (ha₀ : ((a₀ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A),
      (residue A ⟨((a₀ : ↥k₀) : (AlgebraicClosure ℚ)), ha₀⟩) ^ q =
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hjR⟩) := by sorry
