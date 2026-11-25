-- Prove2me | Theorems.Thm_GlobalTheory_T_truncatedMonomials_linearIndependent_over_constants
-- name    : GlobalTheory.T.truncatedMonomials_linearIndependent_over_constants
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:00:09.292981+00:00
-- url     : https://prove2.me/theorems/409acc66-b6fb-4086-93cb-5fb5dec1578f
-- title:
--   T: truncated Monomials linear Independent over constants
-- statement:
--   The T construction uses the truncated Monomials linear Independent over constants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedMonomialsLinearIndependentOverConstantsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedMonomialsLinearIndependentOverConstantsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedMonomialsLinearIndependentOverConstants
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedMonomialsLinearIndependentOverConstantsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.truncatedMonomials_linearIndependent_over_constants : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] (d : ℕ) (x : Fin d → A) (E : Fin d → Derivation k A A), (∀ i j, E i (x j) = if i = j then 1 else 0) → ∀ B : Subalgebra k A, (∀ i, ∀ b ∈ B, E i b = 0) → LinearIndependent B (fun a : Fin d → Fin p => ∏ i, x i ^ (a i : ℕ)) := by sorry
