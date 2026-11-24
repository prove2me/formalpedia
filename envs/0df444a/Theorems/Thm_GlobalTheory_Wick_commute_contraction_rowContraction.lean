-- Prove2me | Theorems.Thm_GlobalTheory_Wick_commute_contraction_rowContraction
-- name    : GlobalTheory.Wick.commute_contraction_rowContraction
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:41.815824+00:00
-- url     : https://prove2.me/theorems/fd4adc5b-b0be-4d0e-8742-e64e6565cc78
-- title:
--   Wick: commute contraction row Contraction
-- statement:
--   The Wick construction uses the commute contraction row Contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L273-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L273-L277

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Wick
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}
variable [Fintype κ]
variable [Fintype ι]

theorem GlobalTheory.Wick.commute_contraction_rowContraction (γ : ι → κ → R) (i : ι) :
    Commute (contraction γ) (rowContraction γ i) := by sorry
