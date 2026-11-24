-- Prove2me | Theorems.Thm_GlobalTheory_TwoVarValRing_not_X_one_dvd_subst
-- name    : GlobalTheory.TwoVarValRing.not_X_one_dvd_subst
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:35.212362+00:00
-- url     : https://prove2.me/theorems/8402d066-ab61-4093-9b54-286e1f9c4d10
-- title:
--   Two Var Val Ring: not X one dvd subst
-- statement:
--   The Two Var Val Ring construction uses the not X one dvd subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLocalRingSecondVariable.lean#L34-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLocalRingSecondVariable.lean#L34-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalRingSecondVariable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TwoVarValRing

theorem GlobalTheory.TwoVarValRing.not_X_one_dvd_subst (k : Type) [Field k] (b : PowerSeries k) (hb : b ≠ 0) :
    ¬ MvPowerSeries.X 1 ∣ b.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) := by sorry
