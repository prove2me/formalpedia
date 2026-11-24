-- Prove2me | Theorems.Thm_GlobalTheory_intCast_mulVec_complex
-- name    : GlobalTheory.intCast_mulVec_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:57.864807+00:00
-- url     : https://prove2.me/theorems/27ed28f1-bfea-41ff-876d-41637ac427ec
-- title:
--   Global Theory: int Cast mul Vec complex
-- statement:
--   The Global Theory construction uses the int Cast mul Vec complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L42-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c d : Matrix ι ι ℤ}
omit [DecidableEq ι]

theorem GlobalTheory.intCast_mulVec_complex (d : Matrix ι ι ℤ) (x : ι → ℤ) :
    (fun i => ((d *ᵥ x) i : ℂ)) = d.map ((↑) : ℤ → ℂ) *ᵥ fun i => (x i : ℂ) := by sorry
