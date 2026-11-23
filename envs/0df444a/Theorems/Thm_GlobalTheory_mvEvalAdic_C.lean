-- Prove2me | Theorems.Thm_GlobalTheory_mvEvalAdic_C
-- name    : GlobalTheory.mvEvalAdic_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:01.817778+00:00
-- url     : https://prove2.me/theorems/6196cc68-6967-4000-b875-b99ca8eb8677
-- title:
--   Global Theory: mv Eval Adic C
-- statement:
--   The Global Theory construction uses the mv Eval Adic C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L82-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable [Finite σ]

theorem GlobalTheory.mvEvalAdic_C (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (a : A) : mvEvalAdic A J x hx (C a) = algebraMap A S a := by sorry
