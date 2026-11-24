-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_ne_zero_of_isPre
-- name    : GlobalTheory.UnitLemma.Desc.Window.ne_zero_of_isPre
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:26:15.20204+00:00
-- url     : https://prove2.me/theorems/387be34c-d69a-40d2-9d73-7232fb568d0d
-- title:
--   Window: ne zero of is Pre
-- statement:
--   The Window construction uses the ne zero of is Pre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L111-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L111-L120

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

theorem GlobalTheory.UnitLemma.Desc.Window.ne_zero_of_isPre [Fintype ι] {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (i : ι) : e i ≠ 0 := by sorry
