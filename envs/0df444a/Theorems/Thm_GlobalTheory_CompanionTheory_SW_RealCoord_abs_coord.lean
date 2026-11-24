-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_abs_coord
-- name    : GlobalTheory.CompanionTheory.SW.RealCoord.abs_coord
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:07:59.668794+00:00
-- url     : https://prove2.me/theorems/4f85541c-88ae-4bc3-a194-e5361763d9a8
-- title:
--   Real Coord: abs coord
-- statement:
--   The Real Coord construction uses the abs coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdeleHaarMapEqScaledVolume.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdeleHaarMapEqScaledVolume.lean#L31-L34

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RealCoord
open InfinitePlace InfinitePlace.Completion
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem GlobalTheory.CompanionTheory.SW.RealCoord.abs_coord (y : Ainf F) (w : InfinitePlace F) : |coord F y w| = ‖y w‖ := by sorry
