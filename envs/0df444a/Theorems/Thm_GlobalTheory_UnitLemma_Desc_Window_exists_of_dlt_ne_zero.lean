-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_exists_of_dlt_ne_zero
-- name    : GlobalTheory.UnitLemma.Desc.Window.exists_of_dlt_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:26:44.412511+00:00
-- url     : https://prove2.me/theorems/84e2a4f7-0826-43b1-ac4e-bac577091d87
-- title:
--   Window: exists of dlt ne zero
-- statement:
--   The Window construction uses the exists of dlt ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L178-L181

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

theorem GlobalTheory.UnitLemma.Desc.Window.exists_of_dlt_ne_zero {π : ι → B.A} {I : Finset ι} {f : B.A → ℚ} {y : B.A}
    (h : dlt π I f y ≠ 0) : ∃ J ⊆ I, f ((∏ j ∈ J, π j) * y) ≠ 0 := by sorry
