-- Prove2me | Theorems.Thm_GlobalTheory_Wick_contraction_pow_X_inl_mul
-- name    : GlobalTheory.Wick.contraction_pow_X_inl_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:14.943154+00:00
-- url     : https://prove2.me/theorems/22823245-3de1-4213-a833-d8bc65950a3d
-- title:
--   Wick: contraction pow X inl mul
-- statement:
--   The Wick construction uses the contraction pow X inl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L295-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L295-L306

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

theorem GlobalTheory.Wick.contraction_pow_X_inl_mul (γ : ι → κ → R) (n : ℕ) (i : ι) (P : MvPolynomial (ι ⊕ κ) R) :
    (contraction γ ^ (n + 1)) (X (Sum.inl i) * P) =
      X (Sum.inl i) * (contraction γ ^ (n + 1)) P +
        (n + 1) • rowContraction γ i ((contraction γ ^ n) P) := by sorry
