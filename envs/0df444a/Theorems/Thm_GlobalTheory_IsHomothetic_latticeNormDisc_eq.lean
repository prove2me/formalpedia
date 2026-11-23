-- Prove2me | Theorems.Thm_GlobalTheory_IsHomothetic_latticeNormDisc_eq
-- name    : GlobalTheory.IsHomothetic.latticeNormDisc_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:40.216876+00:00
-- url     : https://prove2.me/theorems/a2b5daeb-8fde-45c7-89f7-94f87af5fb83
-- title:
--   Is Homothetic: lattice Norm Disc eq
-- statement:
--   The Is Homothetic construction uses the lattice Norm Disc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L30-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors Real UpperHalfPlane
noncomputable section
open GlobalTheory

theorem GlobalTheory.IsHomothetic.latticeNormDisc_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    latticeNormDisc L' = latticeNormDisc L := by sorry
