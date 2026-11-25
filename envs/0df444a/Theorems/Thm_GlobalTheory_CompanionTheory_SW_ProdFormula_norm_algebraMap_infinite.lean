-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ProdFormula_norm_algebraMap_infinite
-- name    : GlobalTheory.CompanionTheory.SW.ProdFormula.norm_algebraMap_infinite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:37:39.257533+00:00
-- url     : https://prove2.me/theorems/9b48e839-99db-5054-88ac-a1a23abb210a
-- title:
--   Prod Formula: norm algebra Map infinite
-- statement:
--   The Prod Formula construction uses the norm algebra Map infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GlobalUnitScalingHaarProductFormula.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GlobalUnitScalingHaarProductFormula.lean#L27-L32

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
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.ProdFormula.norm_algebraMap_infinite (a : F) :
    ‖algebraMap F (InfiniteAdeleRing F) a‖ = ∏ w : InfinitePlace F, w a ^ w.mult := by sorry
