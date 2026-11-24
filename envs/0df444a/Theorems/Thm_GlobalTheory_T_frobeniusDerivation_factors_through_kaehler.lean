-- Prove2me | Theorems.Thm_GlobalTheory_T_frobeniusDerivation_factors_through_kaehler
-- name    : GlobalTheory.T.frobeniusDerivation_factors_through_kaehler
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:41:06.788008+00:00
-- url     : https://prove2.me/theorems/ab14b4d1-bbaa-4b73-b3ac-e5f16c7f18d5
-- title:
--   T: frobenius Derivation factors through kaehler
-- statement:
--   The T construction uses the frobenius Derivation factors through kaehler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusDerivationFactorsThroughKaehlerStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusDerivationFactorsThroughKaehlerStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehler
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehlerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.frobeniusDerivation_factors_through_kaehler : ∀ {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime] [CharP K p] (φ : K →+ M), (∀ a b : K, φ (a * b) = a ^ p • φ b + b ^ p • φ a) → ∃ f : Ω[K⁄ℤ] →+ M, (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ a, f (KaehlerDifferential.D ℤ K a) = φ a := by sorry
