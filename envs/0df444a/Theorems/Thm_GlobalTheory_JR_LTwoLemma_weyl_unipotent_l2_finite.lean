-- Prove2me | Theorems.Thm_GlobalTheory_JR_LTwoLemma_weyl_unipotent_l2_finite
-- name    : GlobalTheory.JR.LTwoLemma.weyl_unipotent_l2_finite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:51.960271+00:00
-- url     : https://prove2.me/theorems/bc5e85c0-8cb7-4da6-b287-4b86f73b86b7
-- title:
--   LTwo Lemma: weyl unipotent l2 finite
-- statement:
--   The LTwo Lemma construction uses the weyl unipotent l2 finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KirillovVanishingOfLimit.lean#L34-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KirillovVanishingOfLimit.lean#L34-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerBoundBigCellStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHeightSqLintegralLtTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtaleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerFunctionalWeylVanishOfWeylUnipotentZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KirillovVanishingOfLimit
import Theorems.Thm_GlobalTheory_T_unimodularHeight_sq_lintegral_lt_top
import Theorems.Thm_GlobalTheory_T_whittaker_bound_big_cell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LTwoLemma
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.LTwoLemma.weyl_unipotent_l2_finite [Unram F E] (hB1 : type_of% GlobalTheory.T.whittaker_bound_big_cell) (hB2 : type_of% GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top) (A : Et F E) (μ : Measure A.K) (hμ : μ.IsAddHaarMeasure)
    (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    ∫⁻ z, ‖Ψ (wS A.K * nS z)‖ₑ ^ 2 ∂μ < ⊤ := by sorry
