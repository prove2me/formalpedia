-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeInt_continuous_compReal
-- name    : GlobalTheory.CompanionTheory.SW.SizeInt.continuous_compReal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:27.722347+00:00
-- url     : https://prove2.me/theorems/e0ea1332-800d-4a6f-ac2f-08ebe3b24b8e
-- title:
--   Size Int: continuous comp Real
-- statement:
--   The Size Int construction uses the continuous comp Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L16-L18

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrable
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SizeInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.SizeInt.continuous_compReal (hF : IsTotallyReal F) (v : InfinitePlace F) :
    Continuous (compReal hF v) := by sorry
