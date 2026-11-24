-- Prove2me | Theorems.Thm_GlobalTheory_exists_mul_mem_iff_of_mk0_eq
-- name    : GlobalTheory.exists_mul_mem_iff_of_mk0_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:35:25.721708+00:00
-- url     : https://prove2.me/theorems/3a341be6-c31f-4671-aa02-e9eb07e5ea6a
-- title:
--   Global Theory: exists mul mem iff of mk0 eq
-- statement:
--   The Global Theory construction uses the exists mul mem iff of mk0 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L127-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L127-L170

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
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.exists_mul_mem_iff_of_mk0_eq (𝔞 𝔟 𝔡 : (Ideal (𝓞 K))⁰)
    (h : ClassGroup.mk0 𝔡 * ClassGroup.mk0 𝔟 = ClassGroup.mk0 𝔞) :
    ∃ u : K, u ≠ 0 ∧ ∀ t : K, (∀ b ∈ (𝔟 : Ideal (𝓞 K)), ∃ a ∈ (𝔞 : Ideal (𝓞 K)),
      u * t * (b : K) = a) ↔ ∃ d ∈ (𝔡 : Ideal (𝓞 K)), t = d := by sorry
