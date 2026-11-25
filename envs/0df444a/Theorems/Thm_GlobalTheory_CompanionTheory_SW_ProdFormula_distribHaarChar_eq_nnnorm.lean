-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ProdFormula_distribHaarChar_eq_nnnorm
-- name    : GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:37:56.905425+00:00
-- url     : https://prove2.me/theorems/b7d3a3c2-cb43-5cd9-a2ab-3907190e6518
-- title:
--   Prod Formula: distrib Haar Char eq nnnorm
-- statement:
--   The Prod Formula construction uses the distrib Haar Char eq nnnorm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GlobalUnitScalingHaarProductFormula.lean#L42-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GlobalUnitScalingHaarProductFormula.lean#L42-L69

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

theorem GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (ha : a ≠ 0) :
    distribHaarChar (Fv F v) (Units.mk0 a ha) = ‖a‖₊ := by sorry
