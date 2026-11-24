-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_eq_evalAdic
-- name    : GlobalTheory.ChartRing.eq_evalAdic
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:17.899656+00:00
-- url     : https://prove2.me/theorems/52aeceae-a9e0-496a-8d42-e000dfb02fb1
-- title:
--   Chart Ring: eq eval Adic
-- statement:
--   The Chart Ring construction uses the eq eval Adic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L110-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L110-L111

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

theorem GlobalTheory.ChartRing.eq_evalAdic (φ : A⟦X⟧ →ₐ[A] S) (h : φ X = s) : φ = evalAdic A J hs := by sorry
