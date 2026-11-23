-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_valued_algebraMap
-- name    : GlobalTheory.CompanionTheory.SW.GoodInt.valued_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:51:30.321855+00:00
-- url     : https://prove2.me/theorems/d6d1ff20-67fb-41de-bce8-1abeb40bbbe9
-- title:
--   Good Int: valued algebra Map
-- statement:
--   The Good Int construction uses the valued algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IntegralAlmostAllPlaces.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IntegralAlmostAllPlaces.lean#L7-L9

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodInt

theorem GlobalTheory.CompanionTheory.SW.GoodInt.valued_algebraMap {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by sorry
