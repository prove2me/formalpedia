-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_jShadow_of_inTube
-- name    : ModularCurve.FullLevel.jShadow_of_inTube
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/e33b389e-4c41-5fdb-9103-f0fc68e6ef6a
-- title:
--   Places in a supersingular tube lie in its j-shadow
-- statement:
--   Fix a prime $q$ and a nonzero natural number $M'$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$; write $\kappa$ for its residue field. Assume the subfield $\overline{\mathbb{Q}}$-generated inside $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ by the coefficientwise image of the full level-$M'$ modular function field, `modularFunctionFieldBar M'`, is contained in `fieldBar q M'`, the corresponding base change of the function field of level $q^2M'$ and subgroup `levelH q M'`. Let $R_0$ be a `ConstantReduction` datum for $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` $= \kappa(\hat\jmath, \hat\jmath_{M'})$, assumed to be coefficientwise reduction: every Laurent series $y$ over $A$ whose image in $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ lies in `modularFunctionFieldBar M'` is $R_0$-integral, with residue equal, as a Laurent series over $\kappa$, to the coefficientwise reduction of $y$. Let $s$ be a place of `modularFunctionFieldC κ M'` over $\kappa$ lying in `ssPlaces q M' κ`, i.e. $s$ is rational, an affine geometric place, and $s(\hat\jmath) \in$ `ssJSet q κ`. Let $P$ be a place of `fieldBar q M'` over $\overline{\mathbb{Q}}$, assumed to lie in the tube of $s$: for every $f$ in `modularFunctionFieldBar M'` belonging to $R_0$`.integers` such that every place of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$ at which the element $\hat\jmath$ — the coefficientwise image of the $q$-expansion `jq` — has non-negative order also has non-negative order at $f$, and such that $R_0$`.residue` $f$ lies in the valuation subring of $s$, and for every $a \in A$ whose residue equals $s$ evaluated at $R_0$`.residue` $f$, the difference of $P$ evaluated at the image of $f$ in `fieldBar q M'` and $a$ lies in $A$ and in fact in the maximal ideal of $A$. The conclusion is the conjunction of two clauses, one for $\hat\jmath$ and one for $\hat\jmath_{M'}$, the coefficientwise image of `qExpand ℚ M' jq`: each of these two elements of `modularFunctionFieldBar M'`, viewed in `fieldBar q M'`, lies in the valuation subring of $P$, and for every $a \in A$ whose residue equals $s$ evaluated at `jGeomGen κ M'` (respectively `jNGeomGen κ M'`), the difference of $P$ evaluated at that element and $a$ lies in $A$ and in the maximal ideal of $A$.
--
--   This passes from the "in-tube" condition at a supersingular place $s$ of the level-$M'$ special fibre, formulated for all admissible test functions, to the weaker "$j$-shadow" condition formulated only for the two distinguished generators $\hat\jmath$ and $\hat\jmath_{M'}$: the content is that these two generators are themselves admissible test functions and are regular at $P$. It is used in the assembly of semistable coverings of the full-level modular curve, where the Igusa-type charts must avoid the supersingular tubes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_jShadow_of_inTube.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.jShadow_of_inTube
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) (hs : s ∈ ssPlaces q M' (ResidueField A))
    (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))
    (hP : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ maximalIdeal A)) :
    (((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
        ∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField A) M') →
          ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
            (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧
      ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
        ∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jNGeomGen (ResidueField A) M') →
          ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
            (⟨_, h⟩ : A) ∈ maximalIdeal A)) := by sorry
