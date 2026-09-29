-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_eq_smul_of_residue_eq_zero_of_mem_integers_of_cuspRegular
-- name    : ModularCurve.FullLevel.exists_eq_smul_of_residue_eq_zero_of_mem_integers_of_cuspRegular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/eec2d554-8757-5468-8283-ad95f2709589
-- title:
--   Dividing a cusp-regular function with zero reduction by q
-- statement:
--   Fix a prime $q$, a level $M'\neq 0$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$, i.e. with $q$ a nonunit of $A$. Let $R_0$ be a constant reduction of the field $\overline{\mathbb Q}$-base change `modularFunctionFieldBar M'` of `modularFunctionFieldFull M'` $=\mathbb Q(\mathrm{divisorExpansions}\,M')\subseteq$ `LaurentSeries ℚ` along $A$, with values in `modularFunctionFieldC (ResidueField A) M'`, the subfield of `LaurentSeries (ResidueField A)` generated over the residue field of $A$ by `jqModC` and `jqNModC`; thus $R_0$ consists of a valuation subring $R_0.\mathrm{integers}$, a surjective residue map onto that field with kernel the maximal ideal, a map on places preserving degrees, and the compatibilities with $A$ recorded in `ConstantReduction`. Assume $R_0$ reads $A$-integral expansions coefficientwise: for every $y\in$ `LaurentSeries ↥A` whose coefficientwise image lies in `modularFunctionFieldBar M'`, that image is $R_0$-integral and its residue, viewed as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$. Let $g\in$ `modularFunctionFieldFull M'` be a Laurent series over $\mathbb Q$ whose coefficientwise image $\bar g$ in `modularFunctionFieldBar M'` lies in $R_0.\mathrm{integers}$, is cusp-regular in the sense that for every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ with $P.\mathrm{ord}$ of the image of `jq` nonnegative one has $P.\mathrm{ord}(\bar g)\geq 0$, and satisfies $R_0.\mathrm{residue}(\bar g)=0$. Then there is $g'\in$ `modularFunctionFieldFull M'` with $g=(q:\mathbb Q)\cdot g'$ such that the image of $g'$ is again $R_0$-integral and cusp-regular in the same sense.
--
--   This is the rational divisibility step of the $\mathsf q$-expansion principle in the form needed at full level $M'$: a rational cusp-regular $R_0$-integral function whose constant reduction vanishes is exactly $q$ times another such function, the divisibility being obtained from the integrality and vanishing of its rational $\mathsf q$-coefficients. It feeds the constructions of algebra homomorphisms from the level-$M'$ function field into `modularFunctionFieldC` whose residues realise a prescribed ring homomorphism, both in the general case and in the variant attached to $\Gamma_1$-structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_eq_smul_of_residue_eq_zero_of_mem_integers_of_cuspRegular.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_eq_smul_of_residue_eq_zero_of_mem_integers_of_cuspRegular
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
      ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')))
    (hres : R₀.residue ⟨_, hgi⟩ = 0) :
    ∃ (g' : LaurentSeries ℚ) (hg' : g' ∈ modularFunctionFieldFull M'),
      g = (q : ℚ) • g' ∧
      (⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers ∧
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g', coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg'⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) := by sorry
