-- Prove2me | Theorems.Thm_GlobalTheory_sumElim_mem
-- name    : GlobalTheory.sumElim_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:50.769848+00:00
-- url     : https://prove2.me/theorems/ff7760f5-0b54-4b5b-a4d9-8646274fe8c6
-- title:
--   Global Theory: sum Elim mem
-- statement:
--   The Global Theory construction uses the sum Elim mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L217-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L217-L220

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
variable {A S τ ι : Type*} [CommRing A] [CommRing S] [Algebra A S]

theorem GlobalTheory.sumElim_mem {K : Ideal S} {u : τ → S} {s : ι → S} (hu : ∀ k, u k ∈ K)
    (hs : ∀ i, s i ∈ K) : ∀ v, Sum.elim u s v ∈ K := by sorry
