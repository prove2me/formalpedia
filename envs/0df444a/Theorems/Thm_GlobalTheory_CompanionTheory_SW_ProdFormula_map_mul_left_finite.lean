-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ProdFormula_map_mul_left_finite
-- name    : GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_finite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:00:43.854692+00:00
-- url     : https://prove2.me/theorems/09d70ac2-10da-44d5-ae20-9ddae91ab9cd
-- title:
--   Prod Formula: map mul left finite
-- statement:
--   The Prod Formula construction uses the map mul left finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GlobalUnitScalingHaarProductFormula.lean#L71-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GlobalUnitScalingHaarProductFormula.lean#L71-L83

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
open HeckeCharacterZeroLocus.SiegelWeilU
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_finite (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (ha : a ≠ 0)
    (μ : Measure (Fv F v)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun x => a * x) = (‖a‖₊)⁻¹ • μ := by sorry
