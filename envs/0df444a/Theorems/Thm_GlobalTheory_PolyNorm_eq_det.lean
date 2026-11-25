-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_eq_det
-- name    : GlobalTheory.PolyNorm.eq_det
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:38.079516+00:00
-- url     : https://prove2.me/theorems/8d99ce0b-338c-5a5a-9e6c-3eb6fac2fa95
-- title:
--   Poly Norm: eq det
-- statement:
--   The Poly Norm construction uses the eq det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L248-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L248-L316

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm

theorem GlobalTheory.PolyNorm.eq_det : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (U : Matrix (Fin m) (Fin m) ℤ_[l]) (N : Polynomial ℤ → ℚ) (Good : Polynomial ℤ → Prop), (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous m ∧ ∀ a : Fin r → ℤ, N (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) → N 1 = 1 → (∀ F, ∀ᶠ t : ℕ in Filter.atTop, Good (F + t)) → (∀ F G, Good F → Good G → N (F * G) = N F * N G) → (∀ F, Good F → ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖) → ∀ F, ((N F : ℚ) : ℚ_[l]) = ((Polynomial.aeval U F).det : ℤ_[l]) := by sorry
