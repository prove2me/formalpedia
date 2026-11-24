-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_exists_punctured_ball_ne_zero
-- name    : GlobalTheory.CompanionTheory.ComplexSets.DiscCover.exists_punctured_ball_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:21.187554+00:00
-- url     : https://prove2.me/theorems/93b32c15-7062-4c71-a7f7-7ec61ea72e95
-- title:
--   Disc Cover: exists punctured ball ne zero
-- statement:
--   The Disc Cover construction uses the exists punctured ball ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforward.lean#L33-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforward.lean#L33-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets GlobalTheory.CompanionTheory.ComplexSets.DiscCover
open Metric

theorem GlobalTheory.CompanionTheory.ComplexSets.DiscCover.exists_punctured_ball_ne_zero (δ : (Fin 1 → ℂ) → ℂ) (c : Fin 1 → ℂ) (hδ : AnalyticAt ℂ δ c)
    (hne : ¬ ∀ᶠ y in 𝓝 c, δ y = 0) : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ y ∈ ball c ρ₀, y ≠ c → δ y ≠ 0 := by sorry
