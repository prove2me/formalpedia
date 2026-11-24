-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_isCompact_inter_of_cut
-- name    : GlobalTheory.CompanionTheory.ComplexSets.DiscCover.isCompact_inter_of_cut
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:32:41.982538+00:00
-- url     : https://prove2.me/theorems/b2936bd3-20fd-4b51-b804-57541784c2c8
-- title:
--   Disc Cover: is Compact inter of cut
-- statement:
--   The Disc Cover construction uses the is Compact inter of cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforward.lean#L55-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforward.lean#L55-L74

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

theorem GlobalTheory.CompanionTheory.ComplexSets.DiscCover.isCompact_inter_of_cut {σ : Type} [Fintype σ] {Y C Nn : Set (σ → ℂ)} {k : ℕ}
    {f : Fin k → (σ → ℂ) → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) Nn)
    (hY : Y ∩ Nn = {z | z ∈ Nn ∧ ∀ i, f i z = 0}) (hC : IsCompact C) (hsub : C ⊆ Nn) :
    IsCompact (Y ∩ C) := by sorry
