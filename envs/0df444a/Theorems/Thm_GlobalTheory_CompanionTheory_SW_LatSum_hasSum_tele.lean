-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_hasSum_tele
-- name    : GlobalTheory.CompanionTheory.SW.LatSum.hasSum_tele
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:07:09.777091+00:00
-- url     : https://prove2.me/theorems/3f29baa9-4e7e-4b14-8c9c-dc408b1c1c2b
-- title:
--   Lat Sum: has Sum tele
-- statement:
--   The Lat Sum construction uses the has Sum tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L8-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L8-L30

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum

theorem GlobalTheory.CompanionTheory.SW.LatSum.hasSum_tele {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + y + 1)) (1 / y) := by sorry
