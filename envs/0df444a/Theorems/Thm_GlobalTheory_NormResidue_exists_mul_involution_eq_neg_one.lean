-- Prove2me | Theorems.Thm_GlobalTheory_NormResidue_exists_mul_involution_eq_neg_one
-- name    : GlobalTheory.NormResidue.exists_mul_involution_eq_neg_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:35:47.048075+00:00
-- url     : https://prove2.me/theorems/311d95ca-5bd9-42ad-9ee1-6326b2bab968
-- title:
--   Norm Residue: exists mul involution eq neg one
-- statement:
--   The Norm Residue construction uses the exists mul involution eq neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsMulInvolutionAddOneMemPow.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsMulInvolutionAddOneMemPow.lean#L7-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsMulInvolutionAddOneMemPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormResidue
open Polynomial

theorem GlobalTheory.NormResidue.exists_mul_involution_eq_neg_one {k : Type*} [Field k] [Finite k] (σ : k →+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (h2 : (2 : k) ≠ 0) :
    ∃ z : k, z * σ z + 1 = 0 := by sorry
