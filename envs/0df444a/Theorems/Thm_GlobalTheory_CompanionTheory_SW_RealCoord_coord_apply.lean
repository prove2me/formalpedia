-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_coord_apply
-- name    : GlobalTheory.CompanionTheory.SW.RealCoord.coord_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:44.731798+00:00
-- url     : https://prove2.me/theorems/1329f347-8c23-4b9f-9368-4ef048ce543d
-- title:
--   Real Coord: coord apply
-- statement:
--   The Real Coord construction uses the coord apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdeleHaarMapEqScaledVolume.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdeleHaarMapEqScaledVolume.lean#L20-L21

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

theorem GlobalTheory.CompanionTheory.SW.RealCoord.coord_apply (y : Ainf F) (w : InfinitePlace F) :
    coord F y w = ringEquivRealOfIsReal (IsTotallyReal.isReal w) (y w) := by sorry
