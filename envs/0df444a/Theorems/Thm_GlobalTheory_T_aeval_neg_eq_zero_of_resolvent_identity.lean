-- Prove2me | Theorems.Thm_GlobalTheory_T_aeval_neg_eq_zero_of_resolvent_identity
-- name    : GlobalTheory.T.aeval_neg_eq_zero_of_resolvent_identity
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:35:26.045663+00:00
-- url     : https://prove2.me/theorems/733c8711-11bb-5fdf-8ce2-24ed393a8082
-- title:
--   T: aeval neg eq zero of resolvent identity
-- statement:
--   The T construction uses the aeval neg eq zero of resolvent identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AevalNegEqZeroOfResolventIdentityStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AevalNegEqZeroOfResolventIdentityStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AevalNegEqZeroOfResolventIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AevalNegEqZeroOfResolventIdentityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.aeval_neg_eq_zero_of_resolvent_identity : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (p : Polynomial ℂ), (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = p.eval u • w) → Polynomial.aeval (-Ω) p = 0 ∧ ∀ (α : ℂ) (w : N), Ω w = α • w → ∀ (q : Polynomial ℂ), p = (Polynomial.X + Polynomial.C α) * q → ∀ u : ℂ, X u w = q.eval u • w := by sorry
