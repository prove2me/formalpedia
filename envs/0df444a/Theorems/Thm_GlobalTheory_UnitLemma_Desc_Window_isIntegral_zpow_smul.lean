-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_isIntegral_zpow_smul
-- name    : GlobalTheory.UnitLemma.Desc.Window.isIntegral_zpow_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:25.811601+00:00
-- url     : https://prove2.me/theorems/b1b9776d-53f4-4d83-9cf5-b31e359038ae
-- title:
--   Window: is Integral zpow smul
-- statement:
--   The Window construction uses the is Integral zpow smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean#L25-L28

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

theorem GlobalTheory.UnitLemma.Desc.Window.isIntegral_zpow_smul (a : K.O) {n : ℤ} (hn : 0 ≤ n) {y : B.A} (hy : IsIntegral K.O y) :
    IsIntegral K.O (al K a ^ n • y) := by sorry
