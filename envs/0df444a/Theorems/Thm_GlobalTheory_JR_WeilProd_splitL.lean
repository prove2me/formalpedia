-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilProd_splitL
-- name    : GlobalTheory.JR.WeilProd.splitL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:58.112922+00:00
-- url     : https://prove2.me/theorems/d6f236eb-5504-4577-9af8-eca59c8142ac
-- title:
--   Weil Prod: split L
-- statement:
--   The Weil Prod construction uses the split L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilConditionProductSplitting.lean#L58-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilConditionProductSplitting.lean#L58-L74

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

theorem GlobalTheory.JR.WeilProd.splitL [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (y : A.L) :
    eK (A.NL y) = (A₁.NL (eL y).1, A₂.NL (eL y).2) ∧
      eK (Algebra.trace A.K A.L y) = (Algebra.trace A₁.K A₁.L (eL y).1, Algebra.trace A₂.K A₂.L (eL y).2) := by sorry
