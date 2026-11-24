-- Prove2me | Theorems.Thm_GlobalTheory_fromBlocks_map_intCast_mem_symplecticGroup
-- name    : GlobalTheory.fromBlocks_map_intCast_mem_symplecticGroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:05.354524+00:00
-- url     : https://prove2.me/theorems/7665f968-709f-4fb6-81d6-b62b318c7270
-- title:
--   Global Theory: from Blocks map int Cast mem symplectic Group
-- statement:
--   The Global Theory construction uses the from Blocks map int Cast mem symplectic Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L72-L80

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

theorem GlobalTheory.fromBlocks_map_intCast_mem_symplecticGroup (R : Type*) [CommRing R]
    (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) :
    fromBlocks (a.map ((↑) : ℤ → R)) (b.map (↑)) (c.map (↑)) (d.map (↑)) ∈
      symplecticGroup ι R := by sorry
