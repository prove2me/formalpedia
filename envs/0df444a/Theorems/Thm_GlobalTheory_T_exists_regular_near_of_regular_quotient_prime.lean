-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_regular_near_of_regular_quotient_prime
-- name    : GlobalTheory.T.exists_regular_near_of_regular_quotient_prime
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:38:57.537176+00:00
-- url     : https://prove2.me/theorems/8c62c9dd-c77f-4f58-a0e9-6302a5bf8ef9
-- title:
--   T: exists regular near of regular quotient prime
-- statement:
--   The T construction uses the exists regular near of regular quotient prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularNearOfRegularQuotientPrimeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularNearOfRegularQuotientPrimeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularNearOfRegularQuotientPrime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularNearOfRegularQuotientPrimeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_regular_near_of_regular_quotient_prime : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (p : Ideal B) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) → IsRegularLocalRing (Localization.AtPrime q) := by sorry
