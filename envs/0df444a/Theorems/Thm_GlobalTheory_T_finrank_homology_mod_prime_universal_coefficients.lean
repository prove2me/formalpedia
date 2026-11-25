-- Prove2me | Theorems.Thm_GlobalTheory_T_finrank_homology_mod_prime_universal_coefficients
-- name    : GlobalTheory.T.finrank_homology_mod_prime_universal_coefficients
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:46.428273+00:00
-- url     : https://prove2.me/theorems/45f9358a-20ee-44cc-a9dc-4220c07360a7
-- title:
--   T: finrank homology mod prime universal coefficients
-- statement:
--   The T construction uses the finrank homology mod prime universal coefficients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankHomologyModPrimeUniversalCoefficientsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankHomologyModPrimeUniversalCoefficientsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankHomologyModPrimeUniversalCoefficients
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankHomologyModPrimeUniversalCoefficientsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finrank_homology_mod_prime_universal_coefficients : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → (∀ n, Module.Finite ℤ (C.homology n)) → ∀ n : ℕ, (Module.finrank (ZMod p) ((((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))) - Module.finrank ℤ (C.homology (n + 1)) := by sorry
