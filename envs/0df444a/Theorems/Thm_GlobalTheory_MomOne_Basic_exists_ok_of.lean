-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_Basic_exists_ok_of
-- name    : GlobalTheory.MomOne.Basic.exists_ok_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:26:40.823286+00:00
-- url     : https://prove2.me/theorems/0b7d2e2c-0774-473b-953f-96c4d420b5cd
-- title:
--   Basic: exists ok of
-- statement:
--   The Basic construction uses the exists ok of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L273-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L273-L301

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
open GlobalTheory.MomOne.Basic
open Filter Topology

theorem GlobalTheory.MomOne.Basic.exists_ok_of (ι : ℂ ≃+* ℂ_[q]) (W : WeierstrassCurve ℂ_[q]) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1) :
    ∃ (L : PeriodPair) (c : ℂ), Mdl.Ok ⟨ι, L, c, W⟩ := by sorry
