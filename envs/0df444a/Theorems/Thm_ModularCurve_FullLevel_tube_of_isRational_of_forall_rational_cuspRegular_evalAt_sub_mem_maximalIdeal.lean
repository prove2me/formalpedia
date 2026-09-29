-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal
-- name    : ModularCurve.FullLevel.tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/8f52de88-ef00-56fe-95ac-c6c4dd2be863
-- title:
--   Rational test functions detect the tube of a supersingular place
-- statement:
--   Fix a prime $q$ and a non-zero natural number $M'$ with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, in the sense that $q$ is a non-unit of $A$; write $\kappa = \mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\kappa$-the field $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\,q\,M'\,\kappa$ (rational affine geometric places whose value at $\mathrm{jGeomGen}$ lies in $\mathrm{ssJSet}\,q\,\kappa$), let $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ inside $\mathrm{LaurentSeries}(\overline{\mathbb Q})$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in $\mathrm{modularFunctionFieldC}\,\kappa\,M'$, assumed compatible with coefficientwise reduction: every Laurent series $y$ over $A$ whose image in $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ lies in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral, and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Let $s \in W$ and let $P$ be a place of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$ that is rational, i.e. $\overline{\mathbb Q}$ maps onto the residue field of $P$. The hypothesis is a test over rational $q$-expansions: for every $g$ in $\mathrm{modularFunctionFieldFull}\,M' \subseteq \mathrm{LaurentSeries}(\mathbb Q)$ whose coefficientwise image in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral, if $\mathrm{ord}_{P'}(g) \ge 0$ at every place $P'$ of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ at which $\mathrm{ord}_{P'}(jq) \ge 0$, and if the $R_0$-residue of $g$ lies in the valuation subring of $s$, then the image of $g$ in $\mathrm{fieldBar}\,q\,M'$ lies in the valuation subring of $P$ and, for every $a \in A$ whose residue in $\kappa$ is the value at $s$ of the $R_0$-residue of $g$, the difference $\mathrm{evalAt}_P(g) - a$ lies in $A$ and in its maximal ideal. The conclusion transfers this to arbitrary coefficients: for every $R_0$-integral $f \in \mathrm{modularFunctionFieldBar}\,M'$ satisfying the same regularity condition relative to $jq$ and whose $R_0$-residue lies in the valuation subring of $s$, and every $a \in A$ whose residue equals the value at $s$ of that $R_0$-residue, the element $\mathrm{evalAt}_P(f) - a$ lies in $A$ and in the maximal ideal of $A$.
--
--   This is the statement that membership of a rational place $P$ of the level-$q^2M'$ field in the residue tube (formal fibre) of a supersingular place $s$ of the special fibre at $q$ is already detected by functions with rational $q$-expansions, the reduction theory behind it being Deuring's pointwise reduction of function fields along a place of the constant field. It feeds the construction of node centres for the layered node rings attached to the Igusa separating model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open ModularCurve.FullLevel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
    (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')) (hP : P.IsRational)

    (htest : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
          ∃ h : P.evalAt (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
            (⟨_, h⟩ : A) ∈ maximalIdeal A) :

    ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
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
