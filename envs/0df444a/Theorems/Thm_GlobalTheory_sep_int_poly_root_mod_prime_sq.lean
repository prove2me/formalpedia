-- Prove2me | Theorems.Thm_GlobalTheory_sep_int_poly_root_mod_prime_sq
-- name    : GlobalTheory.sep_int_poly_root_mod_prime_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:43.726306+00:00
-- url     : https://prove2.me/theorems/09fe2d45-6a72-4eb4-a6b2-d2613d6c9554
-- title:
--   Global Theory: sep int poly root mod prime sq
-- statement:
--   The Global Theory construction uses the sep int poly root mod prime sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SepIntPolyRootModPrimeSq.lean#L34-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SepIntPolyRootModPrimeSq.lean#L34-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLargePrimeDvdIntPolynomialEvalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory
open Polynomial

theorem GlobalTheory.sep_int_poly_root_mod_prime_sq :
    ∀ f : ℤ[X], 0 < f.natDegree → (f.map (Int.castRingHom ℚ)).Separable →
      ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, ((p : ℤ) ^ 2) ∣ f.eval x := by sorry
