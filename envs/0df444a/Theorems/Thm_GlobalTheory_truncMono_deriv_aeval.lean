-- Prove2me | Theorems.Thm_GlobalTheory_truncMono_deriv_aeval
-- name    : GlobalTheory.truncMono_deriv_aeval
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:52.383+00:00
-- url     : https://prove2.me/theorems/601d7e93-56cb-44a5-9641-196b14ee4a66
-- title:
--   Global Theory: trunc Mono deriv aeval
-- statement:
--   The Global Theory construction uses the trunc Mono deriv aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedMonomialsLinearIndependentOverConstants.lean#L8-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedMonomialsLinearIndependentOverConstants.lean#L8-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedMonomialsLinearIndependentOverConstants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open MvPolynomial

theorem GlobalTheory.truncMono_deriv_aeval {k A : Type} [Field k] [CommRing A] [Algebra k A] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) (i : Fin d) (F : MvPolynomial (Fin d) B) :
    E i (aeval x F) = aeval x (pderiv i F) := by sorry
