-- Prove2me | Theorems.Thm_GlobalTheory_T_global_unit_scaling_haar_product_formula
-- name    : GlobalTheory.T.global_unit_scaling_haar_product_formula
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:57.35282+00:00
-- url     : https://prove2.me/theorems/d781d5b8-fb98-520e-9f8e-bb50e1a7542d
-- title:
--   T: global unit scaling haar product formula
-- statement:
--   The T construction uses the global unit scaling haar product formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GlobalUnitScalingHaarProductFormulaStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GlobalUnitScalingHaarProductFormulaStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GlobalUnitScalingHaarProductFormula
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GlobalUnitScalingHaarProductFormulaStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.global_unit_scaling_haar_product_formula : ∀ (F : Type) [Field F] [NumberField F] (a : F), a ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => algebraMap F (Ainf F) a * x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => algebraMap F (Fv F v) a * x) = c v • μ := by sorry
