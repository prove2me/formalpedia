-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_ne_zero
-- name    : GlobalTheory.CompanionTheory.SW.UnitProdAlg.ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:49.660799+00:00
-- url     : https://prove2.me/theorems/5590fe2b-cb4b-44d8-8edd-cdfcc8c42933
-- title:
--   Unit Prod Alg: ne zero
-- statement:
--   The Unit Prod Alg construction uses the ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitProductClosureProperties.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitProductClosureProperties.lean#L45-L47

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitProductClosureProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitProdAlg
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.UnitProdAlg.ne_zero {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) : a ≠ 0 := by sorry
