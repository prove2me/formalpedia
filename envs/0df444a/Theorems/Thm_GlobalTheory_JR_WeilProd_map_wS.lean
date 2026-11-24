-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilProd_map_wS
-- name    : GlobalTheory.JR.WeilProd.map_wS
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:38:20.562868+00:00
-- url     : https://prove2.me/theorems/fd20cf17-2dd3-46e0-b664-95e9560c43e9
-- title:
--   Weil Prod: map w S
-- statement:
--   The Weil Prod construction uses the map w S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilConditionProductSplitting.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilConditionProductSplitting.lean#L152-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIteratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.WeilProd.map_wS {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    SpecialLinearGroup.map f (wS R) = wS S := by sorry
