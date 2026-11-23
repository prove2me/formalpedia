-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Primes_summable_one_div_absNorm_sq
-- name    : GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:39.773299+00:00
-- url     : https://prove2.me/theorems/3db3f96f-cb35-43eb-be93-4be3940e590a
-- title:
--   Primes: summable one div abs Norm sq
-- statement:
--   The Primes construction uses the summable one div abs Norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SummableOneDivAbsNormSq.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SummableOneDivAbsNormSq.lean#L10-L19

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SummableOneDivAbsNormSq
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Primes

theorem GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq :
    ∀ (F : Type) [Field F] [NumberField F],
      Summable fun v : HeightOneSpectrum (𝓞 F) => 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by sorry
