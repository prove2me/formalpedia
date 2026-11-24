-- Prove2me | Theorems.Thm_GlobalTheory_GammaOneProof_rep_smul
-- name    : GlobalTheory.GammaOneProof.rep_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:49:56.643134+00:00
-- url     : https://prove2.me/theorems/116a8f7c-736d-403a-8830-485bbf4b4b47
-- title:
--   Gamma One Proof: rep smul
-- statement:
--   The Gamma One Proof construction uses the rep smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilConstantStandardHermitianEqOne.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilConstantStandardHermitianEqOne.lean#L24-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianLatticeIsOpenIsCompactTestStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KerLEqTraceDotProductOfIsIsomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PsiKMulNLEqOneOnIntegralLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierIndicatorHermitianIntegralLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConstantStandardHermitianEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GammaOneProof

theorem GlobalTheory.GammaOneProof.rep_smul {G X : Type} [Group G] [TopologicalSpace X] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W)
    (g : G) (c : ℂ) {f : X → ℂ} (hf : IsTest f) : W g (c • f) = c • W g f := by sorry
