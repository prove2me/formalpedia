-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeInt_secondCountable_Ainf
-- name    : GlobalTheory.CompanionTheory.SW.SizeInt.secondCountable_Ainf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:20.562383+00:00
-- url     : https://prove2.me/theorems/9d3e8230-e465-4bf8-8c45-471cf84117fa
-- title:
--   Size Int: second Countable Ainf
-- statement:
--   The Size Int construction uses the second Countable Ainf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L29-L32

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

theorem GlobalTheory.CompanionTheory.SW.SizeInt.secondCountable_Ainf (hF : IsTotallyReal F) : SecondCountableTopology (Ainf F) := by sorry
