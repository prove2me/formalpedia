-- Prove2me | Theorems.Thm_GlobalTheory_Wick_contraction_X_inl_mul
-- name    : GlobalTheory.Wick.contraction_X_inl_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:32.066161+00:00
-- url     : https://prove2.me/theorems/4b05a36a-ad38-4b51-aea8-8635da68e1ec
-- title:
--   Wick: contraction X inl mul
-- statement:
--   The Wick construction uses the contraction X inl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L289-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L289-L293

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

theorem GlobalTheory.Wick.contraction_X_inl_mul (γ : ι → κ → R) (i : ι) (P : MvPolynomial (ι ⊕ κ) R) :
    contraction γ (X (Sum.inl i) * P) = X (Sum.inl i) * contraction γ P + rowContraction γ i P := by sorry
