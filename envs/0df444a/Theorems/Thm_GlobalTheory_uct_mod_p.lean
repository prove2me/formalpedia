-- Prove2me | Theorems.Thm_GlobalTheory_uct_mod_p
-- name    : GlobalTheory.uct_mod_p
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:02.094933+00:00
-- url     : https://prove2.me/theorems/192ab9a8-9ea3-47a3-b15b-c26ca78fe393
-- title:
--   Global Theory: uct mod p
-- statement:
--   The Global Theory construction uses the uct mod p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankHomologyModPrimeUniversalCoefficients.lean#L11-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankHomologyModPrimeUniversalCoefficients.lean#L11-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardQuotPrimeSmulEqCardKerMulPowFinrankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyOfShortExactMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiplesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyRestrictScalarsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankHomologyModPrimeUniversalCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.uct_mod_p : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → (∀ n, Module.Finite ℤ (C.homology n)) → ∀ n : ℕ, (Module.finrank (ZMod p) ((((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))) - Module.finrank ℤ (C.homology (n + 1)) := by sorry
