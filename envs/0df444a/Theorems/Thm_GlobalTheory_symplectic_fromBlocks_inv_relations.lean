-- Prove2me | Theorems.Thm_GlobalTheory_symplectic_fromBlocks_inv_relations
-- name    : GlobalTheory.symplectic_fromBlocks_inv_relations
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:09.178795+00:00
-- url     : https://prove2.me/theorems/cadb8068-394a-4b43-81a6-00e49293bd63
-- title:
--   Global Theory: symplectic from Blocks inv relations
-- statement:
--   The Global Theory construction uses the symplectic from Blocks inv relations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L82-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L82-L93

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

theorem GlobalTheory.symplectic_fromBlocks_inv_relations {R : Type*} [CommRing R] {a b c d : Matrix ι ι R}
    (h : fromBlocks a b c d ∈ symplecticGroup ι R) (hd : IsUnit d.det) :
    (b * d⁻¹).IsSymm ∧ (d⁻¹ * c).IsSymm ∧ cᵀ * (b * d⁻¹) = aᵀ - d⁻¹ := by sorry
