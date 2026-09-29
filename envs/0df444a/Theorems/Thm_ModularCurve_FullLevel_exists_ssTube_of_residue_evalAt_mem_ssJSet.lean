-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_ssTube_of_residue_evalAt_mem_ssJSet
-- name    : ModularCurve.FullLevel.exists_ssTube_of_residue_evalAt_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/b44cc0b0-c319-5b3d-9aab-6d4b3ef4055c
-- title:
--   Rational places with supersingular j lie in a supersingular tube
-- statement:
--   Fix a prime $q \ge 5$, a nonzero natural number $M'$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$; write $\kappa$ for its residue field. Let $W$ be a finite set of places of the intermediate field $\mathrm{modularFunctionFieldC}\,\kappa\,M' \subseteq \kappa((\mathsf q))$ over $\kappa$ whose members are exactly the supersingular places, i.e. the places $w$ that are rational ($\kappa$ surjects onto the residue field of $w$), satisfy `IsAffineGeomPlace`, and have $w.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M') \in \mathrm{ssJSet}\,q\,\kappa$, the set of $j$ for which every elliptic curve of that $j$-invariant has no nonzero $q$-torsion point. Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ inside $\overline{\mathbb Q}((\mathsf q))$, and let $R_0$ be a `ConstantReduction` of $\mathrm{modularFunctionFieldBar}\,M'$ over $A$ with values in $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ (a valuation subring $R_0.\mathrm{integers}$, a surjective residue homomorphism onto it with kernel the maximal ideal, a degree-preserving map on places, and the compatibilities of that structure), subject to `hR₀`: every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}((\mathsf q))$ lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0.\mathrm{integers}$, and its $R_0$-residue is, as a Laurent series over $\kappa$, the coefficientwise reduction of $y$. Let $j$ denote the element of $\mathrm{fieldBar}\,q\,M'$ obtained from the coefficientwise image of $\mathrm{jq}$ in $\mathrm{modularFunctionFieldBar}\,M'$. The conclusion: for every place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$ that is rational, such that $j$ lies in the valuation subring of $P$, $P.\mathrm{evalAt}(j) \in A$, and the residue of $P.\mathrm{evalAt}(j)$ lies in $\mathrm{ssJSet}\,q\,\kappa$, there is $s \in W$ with the following property: for every $f \in R_0.\mathrm{integers}$ such that $f$ has nonnegative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ at which $j$ has nonnegative order, and such that the $R_0$-residue of $f$ lies in the valuation subring of $s$, and for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that residue of $f$, the difference $P.\mathrm{evalAt}(f) - a$ lies in $A$ and in fact in the maximal ideal of $A$.
--
--   This is the reduction-place half of the supersingular-tube dichotomy for the full-level field: a rational place of $\mathrm{fieldBar}\,q\,M'$ at which the modular invariant is regular, $A$-integral and supersingular modulo the maximal ideal is congruent, on all of $R_0.\mathrm{integers}$ regular away from the poles of $j$, to the evaluation at a supersingular place of the level-$M'$ field in characteristic $q$. It is used by [`ModularCurve.FullLevel.map_jChartFin_not_mem_ssJSet_of_centred_of_forall_not_ssTube_twoChartIntegralModel`](thm.html#ModularCurve.FullLevel.map_jChartFin_not_mem_ssJSet_of_centred_of_forall_not_ssTube_twoChartIntegralModel), which converts the absence of such a tube into non-supersingularity of the $j$-invariant read off a centred chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_ssTube_of_residue_evalAt_mem_ssJSet.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open ModularCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_ssTube_of_residue_evalAt_mem_ssJSet
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y) :

    ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
      ∀ (hjP : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ P.toValuationSubring) (hjA : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ A),
        IsLocalRing.residue ↥A ⟨_, hjA⟩ ∈ ModularCurve.ssJSet q (ResidueField ↥A) →
      ∃ s : ↥W, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
                (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                  0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
                (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                  ∀ a : A, residue A a =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                    ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                      (⟨_, h⟩ : A) ∈ maximalIdeal A := by sorry
