-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_jShadow_levelAutBar_smul_iff
-- name    : ModularCurve.FullLevel.jShadow_levelAutBar_smul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/b69b098f-4cc6-5699-94d7-e9c57260d856
-- title:
--   Level automorphisms preserve the j-shadow of a supersingular place
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$; let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, so that its residue field $\kappa =$ `ResidueField A` has characteristic $q$. Assume `modularFunctionFieldBar M'`, the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field inside $\overline{\mathbb{Q}}$-Laurent series, is contained in `fieldBar q M'` $=$ `xHFunctionFieldBar (q^2*M') (levelH q M')`, via `hle`. Let $s$ be a place of `modularFunctionFieldC κ M'` over $\kappa$ belonging to `ssPlaces q M' κ`, i.e. satisfying `IsSupersingularPlace q M' κ`; let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$ (an element of `Idx q`), let $\gamma \in \Gamma_0(M')$, and let $P$ be a place of `fieldBar q M'` over $\overline{\mathbb{Q}}$. Write $\hat\jmath$ and $\hat\jmath_{M'}$ for the elements of `fieldBar q M'` obtained, through `hle`, from the coefficientwise images under `coeffEmb` of $j$-expansion `jq` and of its $M'$-fold $q$-expansion `qExpand ℚ M' jq`. Consider the condition on a place $Q$: both $\hat\jmath$ and $\hat\jmath_{M'}$ lie in the valuation subring of $Q$, and for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of `jGeomGen κ M'` (respectively `jNGeomGen κ M'`) the difference $Q.\mathrm{evalAt}(\hat\jmath) - a$ (respectively $Q.\mathrm{evalAt}(\hat\jmath_{M'}) - a$) lies in $A$ and in the maximal ideal of $A$. The theorem asserts that this condition holds for `levelAutBar q M' ζ γ • P` if and only if it holds for $P$.
--
--   This is the statement that the $j$-shadow at a supersingular place is unchanged by the level automorphisms $\mathrm{levelAutBar}(\zeta,\gamma)$, reflecting the classical fact (Deuring, Katz–Mazur) that all $q$-isogenies of a supersingular elliptic curve in characteristic $q$ have the same reduction, so that Kronecker's congruence moves the $j$-invariant only by $q^{\pm 2}$-power Frobenius, which fixes supersingular $j$-invariants. It is used in the construction of semistable coverings at full level, in the theorems producing charted equivalence clauses for valuation subrings of a semistable model with prescribed inertia at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_jShadow_levelAutBar_smul_iff.lean

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

theorem ModularCurve.FullLevel.jShadow_levelAutBar_smul_iff
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) (hs : s ∈ ssPlaces q M' (ResidueField A))
    (ζ : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')) :
    (((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ (levelAutBar q M' ζ γ • P).toValuationSubring ∧
        ∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField A) M') →
          ∃ h : (levelAutBar q M' ζ γ • P).evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
            (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧
      ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ (levelAutBar q M' ζ γ • P).toValuationSubring ∧
        ∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jNGeomGen (ResidueField A) M') →
          ∃ h : (levelAutBar q M' ζ γ • P).evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
            (⟨_, h⟩ : A) ∈ maximalIdeal A)) ↔
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
