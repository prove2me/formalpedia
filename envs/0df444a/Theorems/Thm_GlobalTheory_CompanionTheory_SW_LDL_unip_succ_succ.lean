-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_unip_succ_succ
-- name    : GlobalTheory.CompanionTheory.SW.LDL.unip_succ_succ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:07:11.613809+00:00
-- url     : https://prove2.me/theorems/d0d1845c-977d-4197-b25b-74ecebb72b43
-- title:
--   LDL: unip succ succ
-- statement:
--   The LDL construction uses the unip succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOpenChartDiagonalUnipotent.lean#L59-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOpenChartDiagonalUnipotent.lean#L59-L65

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LDL
variable {R K : Type} [CommRing R] [CommRing K]

theorem GlobalTheory.CompanionTheory.SW.LDL.unip_succ_succ {n : ℕ} (u : Up (n + 1) → K) (i j : Fin n) :
    unip u i.succ j.succ = unip (tailU u) i j := by sorry
