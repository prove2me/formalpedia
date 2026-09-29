-- Prove2me | Theorems.Thm_ModularCurve_constantReduction_residue_arithmeticGalois_smul_eq_of_eq_two
-- name    : ModularCurve.constantReduction_residue_arithmeticGalois_smul_eq_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/fe75fddf-f201-5b24-a8a4-2105c46585da
-- title:
--   Inertia preserves residues of a constant reduction (q=2)
-- statement:
--   Fix a prime $q$ together with the hypothesis $q=2$, and a nonzero natural number $M'$ with $q \nmid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that the image of $q$ lies in the nonunits of $A$, and write $\kappa =$ `ResidueField A`. Let $F =$ `modularFunctionFieldBar M'` be the base change to $\overline{\mathbb{Q}}$ of the level-$M'$ modular function field `modularFunctionFieldFull M'` $\subset \mathbb{Q}((q))$, and let $\bar F =$ `modularFunctionFieldC κ M'` be the subfield of $\kappa((q))$ generated over $\kappa$ by `jqModC` and `jqNModC`. Let $R_0$ be a constant reduction of $F$ along $A$ with values in $\bar F$: a valuation subring $R_0.\mathrm{integers}$ of $F$ together with a surjective residue homomorphism onto $\bar F$ whose kernel is the maximal ideal, extending the residue map of $A$, with every nonzero element of $F$ becoming, after scaling by a constant, an integral element of nonzero residue, and with a degree-preserving, order-compatible map on places. Assume $R_0$ is pinned coefficientwise: for every Laurent series $y$ with coefficients in $A$ whose image in $\overline{\mathbb{Q}}((q))$ lies in $F$, that element is $R_0$-integral and its residue, read as an element of $\kappa((q))$, is the coefficientwise reduction of $y$. The conclusion is that for every $\tau$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$, and every $R_0$-integral $f \in F$, the element $\tau \cdot f$ obtained by letting $\tau$ act coefficientwise on $q$-expansions is again $R_0$-integral and has the same residue as $f$.
--
--   This is the $q$-expansion principle step asserting that inertia at $q$ acts trivially on the constant (good) reduction of the level-$M'$ modular function field, in the case $q=2$. It feeds into the analysis of the Drinfeld ring on a component chart, [`ModularCurve.FullLevel.arithmeticGalois_smul_mem_drinfeldRing_iff_of_componentChart_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.arithmeticGalois_smul_mem_drinfeldRing_iff_of_componentChart_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_constantReduction_residue_arithmeticGalois_smul_eq_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.constantReduction_residue_arithmeticGalois_smul_eq_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y) :
    ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hf' : ModularCurve.arithmeticGalois (modularFunctionFieldFull M') τ • f ∈ R₀.integers, R₀.residue ⟨ModularCurve.arithmeticGalois (modularFunctionFieldFull M') τ • f, hf'⟩ = R₀.residue ⟨f, hf⟩ := by sorry
