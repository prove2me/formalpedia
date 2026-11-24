-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_family_ne_zero
-- name    : GlobalTheory.CompanionTheory.SW.UnitProdAlg.family_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:11:51.097519+00:00
-- url     : https://prove2.me/theorems/3260b0ac-c457-4d1f-96dd-fa969f7613dc
-- title:
--   Unit Prod Alg: family ne zero
-- statement:
--   The Unit Prod Alg construction uses the family ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitProductClosureProperties.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitProductClosureProperties.lean#L49-L54

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

theorem GlobalTheory.CompanionTheory.SW.UnitProdAlg.family_ne_zero {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c)
    (v : HeightOneSpectrum (𝓞 F)) : c v ≠ 0 := by sorry
