-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_not_isIntegral_inv_smul_idem
-- name    : GlobalTheory.UnitLemma.Desc.Window.not_isIntegral_inv_smul_idem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:27:17.08099+00:00
-- url     : https://prove2.me/theorems/04d08133-fb1c-46cf-b0c2-146d85902fcf
-- title:
--   Window: not is Integral inv smul idem
-- statement:
--   The Window construction uses the not is Integral inv smul idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L99-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L99-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}

theorem GlobalTheory.UnitLemma.Desc.Window.not_isIntegral_inv_smul_idem {a : K.O} (ha : K.Small a) {f : B.A} (hf : IsIdempotentElem f)
    (h0 : f ≠ 0) : ¬ IsIntegral K.O (al K a ^ (-1 : ℤ) • f) := by sorry
