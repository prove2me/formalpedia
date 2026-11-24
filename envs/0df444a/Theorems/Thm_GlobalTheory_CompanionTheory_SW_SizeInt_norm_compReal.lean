-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeInt_norm_compReal
-- name    : GlobalTheory.CompanionTheory.SW.SizeInt.norm_compReal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:42.227159+00:00
-- url     : https://prove2.me/theorems/f86e8237-d64c-46c4-ac09-da4c11d4457c
-- title:
--   Size Int: norm comp Real
-- statement:
--   The Size Int construction uses the norm comp Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L24-L27

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

theorem GlobalTheory.CompanionTheory.SW.SizeInt.norm_compReal (hF : IsTotallyReal F) (v : InfinitePlace F) (x : v.Completion) :
    ‖compReal hF v x‖ = ‖x‖ := by sorry
