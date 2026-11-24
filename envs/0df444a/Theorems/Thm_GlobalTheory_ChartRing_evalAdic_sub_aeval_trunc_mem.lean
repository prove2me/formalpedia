-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_evalAdic_sub_aeval_trunc_mem
-- name    : GlobalTheory.ChartRing.evalAdic_sub_aeval_trunc_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:04.193962+00:00
-- url     : https://prove2.me/theorems/12e70f8d-ab3a-4f44-8fea-99a05f0c2c77
-- title:
--   Chart Ring: eval Adic sub aeval trunc mem
-- statement:
--   The Chart Ring construction uses the eval Adic sub aeval trunc mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L75-L78

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

theorem GlobalTheory.ChartRing.evalAdic_sub_aeval_trunc_mem (n : ℕ) (f : A⟦X⟧) :
    evalAdic A J hs f - Polynomial.aeval s (trunc n f) ∈ J ^ n := by sorry
