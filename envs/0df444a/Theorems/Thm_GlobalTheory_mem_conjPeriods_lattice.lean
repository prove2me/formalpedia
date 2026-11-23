-- Prove2me | Theorems.Thm_GlobalTheory_mem_conjPeriods_lattice
-- name    : GlobalTheory.mem_conjPeriods_lattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:37.457928+00:00
-- url     : https://prove2.me/theorems/66e028d3-abd5-4aa9-b89e-bfb16ca8243e
-- title:
--   Global Theory: mem conj Periods lattice
-- statement:
--   The Global Theory construction uses the mem conj Periods lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L49-L54

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

theorem GlobalTheory.mem_conjPeriods_lattice (L : PeriodPair) (z : ℂ) :
    z ∈ (conjPeriods L).lattice ↔ starRingEnd ℂ z ∈ L.lattice := by sorry
