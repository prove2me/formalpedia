-- Prove2me | Theorems.Thm_ModularCurve_constantReduction_residue_arithmeticGalois_smul_eq_of_eq_three
-- name    : ModularCurve.constantReduction_residue_arithmeticGalois_smul_eq_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/8e7edf42-4223-5b5c-a91a-dfd5416fc08f
-- title:
--   Inertia acts trivially on residues of the constant reduction (q=3)
-- statement:
--   Fix a prime $q$ with $q = 3$ and a non-zero natural number $M'$ not divisible by $q$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$, and write $\kappa =$ `ResidueField A`. Let $R_0$ be a constant reduction, along $A$, of the field $\overline{\mathbb{Q}}\cdot F(M')$ — the base change to $\overline{\mathbb{Q}}$, inside $\overline{\mathbb{Q}}((q))$, of the level-$M'$ modular function field `modularFunctionFieldFull M'` — with target the subfield `modularFunctionFieldC` of $\kappa((q))$ generated over $\kappa$ by the reductions of the $q$-expansions of $j$ and $j(q^{M'})$; thus $R_0$ consists of a valuation subring `R₀.integers`, a surjective residue homomorphism onto that target whose kernel is the maximal ideal, compatibility with $A$ and its residue map, a scaling condition, and a degree- and order-preserving map on places. Assume $R_0$ is pinned coefficientwise: for every Laurent series $y$ over $A$ whose image in $\overline{\mathbb{Q}}((q))$ lies in $\overline{\mathbb{Q}}\cdot F(M')$, that element is $R_0$-integral and its residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. The conclusion is that for every $\tau$ in the inertia subgroup of $A$ inside $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ (the image of the inertia subgroup of the decomposition subgroup) and every $R_0$-integral $f$, the element $\tau \cdot f$ obtained by applying $\tau$ to the coefficients of the $q$-expansion of $f$ is again $R_0$-integral, with the same $R_0$-residue as $f$.
--
--   This is the $q$-expansion principle in the form needed here: inertia at $q$ acts on $q$-expansions coefficientwise, hence trivially on residues of a constant reduction pinned coefficientwise, so the reduction is defined over the residue field of the inertia-fixed subring. It is the $q = 3$ case of the statement, and is used in the analysis of the Drinfeld ring on a component chart at level divisible by $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_constantReduction_residue_arithmeticGalois_smul_eq_of_eq_three.lean

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

theorem ModularCurve.constantReduction_residue_arithmeticGalois_smul_eq_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y) :
    ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hf' : ModularCurve.arithmeticGalois (modularFunctionFieldFull M') τ • f ∈ R₀.integers, R₀.residue ⟨ModularCurve.arithmeticGalois (modularFunctionFieldFull M') τ • f, hf'⟩ = R₀.residue ⟨f, hf⟩ := by sorry
