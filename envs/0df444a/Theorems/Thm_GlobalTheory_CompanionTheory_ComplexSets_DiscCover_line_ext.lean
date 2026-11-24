-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_line_ext
-- name    : GlobalTheory.CompanionTheory.ComplexSets.DiscCover.line_ext
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:00.946686+00:00
-- url     : https://prove2.me/theorems/86775d85-19ba-4a82-9fe1-2cf9ac924105
-- title:
--   Disc Cover: line ext
-- statement:
--   The Disc Cover construction uses the line ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforward.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforward.lean#L19-L22

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

theorem GlobalTheory.CompanionTheory.ComplexSets.DiscCover.line_ext {y y' : Fin 1 → ℂ} (h : y 0 = y' 0) : y = y' := by sorry
