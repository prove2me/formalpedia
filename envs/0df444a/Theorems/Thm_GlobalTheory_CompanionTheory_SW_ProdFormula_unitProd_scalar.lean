-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ProdFormula_unitProd_scalar
-- name    : GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:37:47.471715+00:00
-- url     : https://prove2.me/theorems/1b2fbd0f-b14d-5107-8559-878869986c4a
-- title:
--   Prod Formula: unit Prod scalar
-- statement:
--   The Prod Formula construction uses the unit Prod scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GlobalUnitScalingHaarProductFormula.lean#L91-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GlobalUnitScalingHaarProductFormula.lean#L91-L135

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GlobalUnitScalingHaarProductFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ProdFormula
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar : ∀ (F : Type) [Field F] [NumberField F] (a : F), a ≠ 0 →
    ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧
      (∀ μ : Measure (Ainf F), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Ainf F) a * x) = cinf • μ) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Fv F v) a * x) = c v • μ := by sorry
