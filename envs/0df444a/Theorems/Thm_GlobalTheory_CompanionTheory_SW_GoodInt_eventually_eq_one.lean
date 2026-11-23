-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_eventually_eq_one
-- name    : GlobalTheory.CompanionTheory.SW.GoodInt.eventually_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:43.373932+00:00
-- url     : https://prove2.me/theorems/5d31ebf0-8427-495c-b78d-243cd8467cad
-- title:
--   Good Int: eventually eq one
-- statement:
--   The Good Int construction uses the eventually eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IntegralAlmostAllPlaces.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IntegralAlmostAllPlaces.lean#L18-L24

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

theorem GlobalTheory.CompanionTheory.SW.GoodInt.eventually_eq_one {F : Type} [Field F] [NumberField F] (x : F) (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x = 1 := by sorry
