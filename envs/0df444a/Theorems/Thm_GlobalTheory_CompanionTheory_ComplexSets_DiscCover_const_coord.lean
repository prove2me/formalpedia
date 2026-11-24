-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_const_coord
-- name    : GlobalTheory.CompanionTheory.ComplexSets.DiscCover.const_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:47.829407+00:00
-- url     : https://prove2.me/theorems/2c17e203-b4ed-4245-995a-50ddc7c30bd4
-- title:
--   Disc Cover: const coord
-- statement:
--   The Disc Cover construction uses the const coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforward.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforward.lean#L15-L17

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

theorem GlobalTheory.CompanionTheory.ComplexSets.DiscCover.const_coord (y : Fin 1 → ℂ) : (fun _ : Fin 1 => y 0) = y := by sorry
