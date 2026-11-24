-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_evalAdic_X
-- name    : GlobalTheory.ChartRing.evalAdic_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:41.270776+00:00
-- url     : https://prove2.me/theorems/36e89adf-1113-4840-b1c4-1c6bbf479603
-- title:
--   Chart Ring: eval Adic X
-- statement:
--   The Chart Ring construction uses the eval Adic X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L86-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable (J : Ideal S) [IsAdicComplete J S] {s : S} (hs : s ∈ J)

theorem GlobalTheory.ChartRing.evalAdic_X : evalAdic A J hs X = s := by sorry
