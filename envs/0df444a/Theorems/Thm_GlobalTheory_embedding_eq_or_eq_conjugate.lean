-- Prove2me | Theorems.Thm_GlobalTheory_embedding_eq_or_eq_conjugate
-- name    : GlobalTheory.embedding_eq_or_eq_conjugate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:00.125897+00:00
-- url     : https://prove2.me/theorems/bb7fdb34-def5-46ae-a23b-8ba7f6147fc4
-- title:
--   Global Theory: embedding eq or eq conjugate
-- statement:
--   The Global Theory construction uses the embedding eq or eq conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L115-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MeanLogCovolumeEqMeanClassGroup.lean#L115-L125

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

theorem GlobalTheory.embedding_eq_or_eq_conjugate (hK : Module.finrank ℚ K = 2) {σ₀ : K →+* ℂ}
    (h₀ : ¬ ComplexEmbedding.IsReal σ₀) (σ : K →+* ℂ) :
    σ = σ₀ ∨ σ = ComplexEmbedding.conjugate σ₀ := by sorry
