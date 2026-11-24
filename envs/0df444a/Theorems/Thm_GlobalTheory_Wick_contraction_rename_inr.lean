-- Prove2me | Theorems.Thm_GlobalTheory_Wick_contraction_rename_inr
-- name    : GlobalTheory.Wick.contraction_rename_inr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:30.982591+00:00
-- url     : https://prove2.me/theorems/ca70c8fb-92ad-45e4-ba73-a31ef108736c
-- title:
--   Wick: contraction rename inr
-- statement:
--   The Wick construction uses the contraction rename inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L279-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L279-L287

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

theorem GlobalTheory.Wick.contraction_rename_inr (γ : ι → κ → R) (q : MvPolynomial κ R) :
    contraction γ (rename Sum.inr q) = 0 := by sorry
