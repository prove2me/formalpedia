-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero
-- name    : ModularCurve.FullLevel.sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/9be2df06-a145-56f8-a60a-3df72dd3d6b9
-- title:
--   Relations among reductions are respected by admissible evaluations
-- statement:
--   Fix a prime $q$ with $5 \le q$ and a nonzero natural number $M'$ not divisible by $q$, together with a valuation subring $A$ of $\overline{\mathbb Q}$ in which $q$ is a nonunit (`A.LiesOverPrime q`). Let $R_0$ be a `ConstantReduction` of $A$ on $\overline{\mathbb Q}\cdot F_{M'} :=$ `modularFunctionFieldBar M'` (the base change to $\overline{\mathbb Q}$ of the Laurent-series field `modularFunctionFieldFull M'`, generated over $\mathbb Q$ by the divisor expansions of level $M'$) with values in `modularFunctionFieldC (ResidueField A) M'`, i.e. a valuation subring $R_0.\mathrm{integers}$, a surjective residue homomorphism onto that field with kernel the maximal ideal, and a degree-preserving map on places satisfying the usual compatibilities with $A$ and with divisors. Assume $hR_0$: every Laurent series $y$ with coefficients in $A$ whose image lies in $\overline{\mathbb Q}\cdot F_{M'}$ lies in $R_0.\mathrm{integers}$ and has residue equal to the coefficientwise reduction of $y$ modulo the maximal ideal of $A$. Let $\mathcal A$ be a subring of $\mathrm{LaurentSeries}\,\mathbb Q$ consisting exactly of those $gf$ which lie in `modularFunctionFieldFull M'`, whose image in $\overline{\mathbb Q}\cdot F_{M'}$ lies in $R_0.\mathrm{integers}$, and which satisfy $0 \le P.\mathrm{ord}(gf)$ at every place $P$ of $\overline{\mathbb Q}\cdot F_{M'}$ over $\overline{\mathbb Q}$ with $0 \le P.\mathrm{ord}(jq)$; assume $jq \in \mathcal A$. Let $\Omega$ be a field which is an algebra over the residue field $\kappa_A$ of $A$, and $\mathrm{val} : \mathcal A \to \Omega$ a ring homomorphism which annihilates every element of $\mathcal A$ whose $R_0$-residue is $0$, and for which $\mathrm{val}(jq)$ is transcendental over $\kappa_A$. The conclusion: for every $n$, every family $gf_1,\dots,gf_n$ of elements of $\mathcal A$ lying in `modularFunctionFieldFull M'` with images in $R_0.\mathrm{integers}$, and all $c_1,\dots,c_n \in \kappa_A$, if $\sum_i c_i \cdot R_0.\mathrm{residue}(gf_i) = 0$ in `modularFunctionFieldC (ResidueField A) M'`, then $\sum_i \mathrm{algebraMap}(c_i)\,\mathrm{val}(gf_i) = 0$ in $\Omega$.
--
--   This is the linearity step in the construction of a reduction map out of the level-$M'$ modular function field in characteristic $q$: any evaluation $\mathrm{val}$ killing functions of vanishing reduction automatically respects all $\kappa_A$-linear relations among the reductions of admissible rational modular functions. It is used by [`ModularCurve.FullLevel.exists_algHom_modularFunctionFieldFullC_of_ringHom_admissible`](thm.html#ModularCurve.FullLevel.exists_algHom_modularFunctionFieldFullC_of_ringHom_admissible) to upgrade such a homomorphism to an algebra homomorphism on the reduced function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero.lean

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
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000
open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups
attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)

    (𝒜 : Subring (LaurentSeries ℚ))
    (h𝒜 : ∀ gf : LaurentSeries ℚ, gf ∈ 𝒜 ↔
      ∃ (hgf : gf ∈ modularFunctionFieldFull M')
        (_ : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M')))
    (hj𝒜 : jq ∈ 𝒜)
    (Ω : Type) [Field Ω] [Algebra (ResidueField A) Ω] (val : ↥𝒜 →+* Ω)
    (hval0 : ∀ (gf : LaurentSeries ℚ) (h : gf ∈ 𝒜) (hgf : gf ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0 → val ⟨gf, h⟩ = 0)
    (hvalj : Transcendental (ResidueField A) (val ⟨jq, hj𝒜⟩)) :
    ∀ (n : ℕ) (gf : Fin n → LaurentSeries ℚ) (h : ∀ i, gf i ∈ 𝒜) (hgf : ∀ i, gf i ∈ modularFunctionFieldFull M')
      (hgi : ∀ i, (⟨coeffEmb (AlgebraicClosure ℚ) (gf i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hgf i)⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
      (c : Fin n → ResidueField A),
      ∑ i, c i • (R₀.residue ⟨_, hgi i⟩ : modularFunctionFieldC (ResidueField A) M') = 0 →
      ∑ i, algebraMap (ResidueField A) Ω (c i) * val ⟨gf i, h i⟩ = 0 := by sorry
