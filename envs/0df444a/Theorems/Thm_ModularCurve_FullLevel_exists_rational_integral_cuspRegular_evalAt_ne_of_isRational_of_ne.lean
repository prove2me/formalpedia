-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne
-- name    : ModularCurve.FullLevel.exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/ab025da3-5d7b-5f55-b00b-9401617ec043
-- title:
--   Rational cusp-regular function separating two reduced rational places
-- statement:
--   Let $q$ be a prime and $M'\ge 1$ with $q\nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, in the sense that the image of $q$ lies in the nonunits of $A$; write $\kappa$ for its residue field. Let $R_0$ be a constant reduction along $A$ of $\overline{\mathbb Q}\cdot\mathbb Q(\text{divisorExpansions}\,M')\subseteq\overline{\mathbb Q}((q))$, namely `modularFunctionFieldBar M'`, onto $\kappa(\bar\jmath_q,\bar\jmath_{q^{M'}})=$ `modularFunctionFieldC κ M'`: thus a valuation subring `R₀.integers`, a surjective residue homomorphism onto the reduced field with kernel the maximal ideal, a map on places, and the compatibilities of `ConstantReduction`. Assume `hR₀`: every Laurent series with coefficients in $A$ whose coefficientwise image lies in `modularFunctionFieldBar M'` is $R_0$-integral, with residue the coefficientwise reduction of that series. Let $s\ne s'$ be places of `modularFunctionFieldC κ M'` over $\kappa$, both rational (the map from $\kappa$ to the residue field of the place is surjective), at which `jGeomGen` is a member of the valuation subring. Then there is a Laurent series $g$ over $\mathbb Q$ lying in `modularFunctionFieldFull M'` whose image in `modularFunctionFieldBar M'` is $R_0$-integral, which satisfies $\operatorname{ord}_P g\ge 0$ at every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ with $\operatorname{ord}_P jq\ge 0$, and whose $R_0$-residue lies in the valuation subrings of $s$ and of $s'$ and has distinct values there: $s.\mathrm{evalAt}(\bar g)\ne s'.\mathrm{evalAt}(\bar g)$.
--
--   This is the separation-of-points step for the reduction in characteristic $q$ of the level-$M'$ modular function field when $q\nmid M'$: two distinct rational places of the reduced field at which the moduli generator $\bar\jmath$ is regular are distinguished by the value of the reduction of a function defined over $\mathbb Q$ which is regular wherever $j$ is. It feeds the identification of places of the reduced curve with moduli points and the comparison with Frobenius used in the results on Tate points and rigid data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open ModularCurve
open ModularCurve.FullLevel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s s' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))
    (hs : s.IsRational) (hs' : s'.IsRational)
    (hjs : jGeomGen (ResidueField A) M' ∈ s.toValuationSubring)
    (hjs' : jGeomGen (ResidueField A) M' ∈ s'.toValuationSubring)
    (hss' : s ≠ s') :
    ∃ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) ∧
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈ s.toValuationSubring ∧
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈ s'.toValuationSubring ∧
      s.evalAt (R₀.residue ⟨_, hgi⟩) ≠ s'.evalAt (R₀.residue ⟨_, hgi⟩) := by sorry
