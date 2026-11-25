-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdeleHaar_exists_haar_integral_one
-- name    : GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:15:05.262615+00:00
-- url     : https://prove2.me/theorems/6bf1ef08-030c-4b7e-835f-fad5dde627ac
-- title:
--   Adele Haar: exists haar integral one
-- statement:
--   The Adele Haar construction uses the exists haar integral one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsFiniteAdeleHaarNormalized.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsFiniteAdeleHaarNormalized.lean#L9-L22

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsFiniteAdeleHaarNormalized
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleHaar

theorem GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one : ∀ (F : Type) [Field F] [NumberField F],
    ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧
      lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 := by sorry
