-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_inv
-- name    : GlobalTheory.CompanionTheory.SW.UnitProdAlg.inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:41.460701+00:00
-- url     : https://prove2.me/theorems/121e3d19-6a5e-4585-9ddd-4c821b56cd07
-- title:
--   Unit Prod Alg: inv
-- statement:
--   The Unit Prod Alg construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitProductClosureProperties.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitProductClosureProperties.lean#L56-L58

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

theorem GlobalTheory.CompanionTheory.SW.UnitProdAlg.inv {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) :
    IsUnitProd a⁻¹ (fun v => (c v)⁻¹) := by sorry
