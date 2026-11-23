-- Prove2me | Theorems.Thm_GlobalTheory_latticeNormDisc_eq
-- name    : GlobalTheory.latticeNormDisc_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:29.210999+00:00
-- url     : https://prove2.me/theorems/d86f7b90-9586-4e1e-bc63-43e22791d45d
-- title:
--   Global Theory: lattice Norm Disc eq
-- statement:
--   The Global Theory construction uses the lattice Norm Disc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L23-L25

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

theorem GlobalTheory.latticeNormDisc_eq (L : PeriodPair) :
    latticeNormDisc L = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ^ 6 * ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ := by sorry
