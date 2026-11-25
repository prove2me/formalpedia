-- Prove2me | Theorems.Thm_GlobalTheory_log_pi_sub_log_latticeNormDisc
-- name    : GlobalTheory.log_pi_sub_log_latticeNormDisc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:10:08.976028+00:00
-- url     : https://prove2.me/theorems/c51cf5ae-f47d-4113-bf45-0e8b6ca58e36
-- title:
--   Global Theory: log pi sub log lattice Norm Disc
-- statement:
--   The Global Theory construction uses the log pi sub log lattice Norm Disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L93-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L93-L109

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

theorem GlobalTheory.log_pi_sub_log_latticeNormDisc {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    Real.log π - Real.log (|(L.ω₁ * starRingEnd ℂ L.ω₂).im| ^ 6 *
        ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖) / 6 =
      -Real.log (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) := by sorry
