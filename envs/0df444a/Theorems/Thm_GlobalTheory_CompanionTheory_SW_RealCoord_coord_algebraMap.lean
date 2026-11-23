-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_coord_algebraMap
-- name    : GlobalTheory.CompanionTheory.SW.RealCoord.coord_algebraMap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:30:52.646155+00:00
-- url     : https://prove2.me/theorems/4656e2bd-9056-431a-aec5-73306a04ba4d
-- title:
--   Real Coord: coord algebra Map
-- statement:
--   The Real Coord construction uses the coord algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdeleHaarMapEqScaledVolume.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdeleHaarMapEqScaledVolume.lean#L39-L45

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

theorem GlobalTheory.CompanionTheory.SW.RealCoord.coord_algebraMap (x : F) (w : InfinitePlace F) :
    coord F (algebraMap F (Ainf F) x) w = rho F w x := by sorry
