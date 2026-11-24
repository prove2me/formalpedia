-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_main
-- name    : GlobalTheory.CompanionTheory.SW.UnitProdAlg.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:52.923851+00:00
-- url     : https://prove2.me/theorems/973a654a-18d4-4bfe-b581-728afefa382b
-- title:
--   Unit Prod Alg: main
-- statement:
--   The Unit Prod Alg construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitProductClosureProperties.lean#L60-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitProductClosureProperties.lean#L60-L79

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

theorem GlobalTheory.CompanionTheory.SW.UnitProdAlg.main : ∀ (F : Type) [Field F] [NumberField F] (a b : ℝ≥0)
    (c e : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd a c → IsUnitProd b e →
    a ≠ 0 ∧ (∀ v, c v ≠ 0) ∧ IsUnitProd (a * b) (fun v => c v * e v) ∧
    IsUnitProd a⁻¹ (fun v => (c v)⁻¹) ∧ IsUnitProd (a / b) (fun v => c v / e v) ∧
    IsUnitProd (NNReal.sqrt a) (fun v => NNReal.sqrt (c v)) ∧
    (∀ n : ℕ, IsUnitProd (a ^ n) (fun v => c v ^ n)) ∧
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by sorry
