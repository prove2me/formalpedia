-- Prove2me | Theorems.Thm_GlobalTheory_Wick_contraction_apply
-- name    : GlobalTheory.Wick.contraction_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:07.282737+00:00
-- url     : https://prove2.me/theorems/69f23769-22a7-4882-99b9-e61d453067be
-- title:
--   Wick: contraction apply
-- statement:
--   The Wick construction uses the contraction apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L264-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L264-L266

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

theorem GlobalTheory.Wick.contraction_apply (γ : ι → κ → R) (P : MvPolynomial (ι ⊕ κ) R) :
    contraction γ P = ∑ i, ∑ j, γ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) P) := by sorry
