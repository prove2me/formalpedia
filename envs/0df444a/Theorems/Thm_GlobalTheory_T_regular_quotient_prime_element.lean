-- Prove2me | Theorems.Thm_GlobalTheory_T_regular_quotient_prime_element
-- name    : GlobalTheory.T.regular_quotient_prime_element
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:26.979942+00:00
-- url     : https://prove2.me/theorems/2e847e7e-0a95-5978-859f-6b6a80fcde02
-- title:
--   T: regular quotient prime element
-- statement:
--   The T construction uses the regular quotient prime element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/RegularQuotientPrimeElement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/RegularQuotientPrimeElement.lean#L5-L6

import Mathlib
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RegularQuotientPrimeElement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_RegularQuotientPrimeElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem GlobalTheory.T.regular_quotient_prime_element : ∀ (A : Type) [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime] (x : A), x ≠ 0 → x ∈ P → IsRegularRing (A ⧸ Ideal.span {x}) → Prime (algebraMap A (Localization.AtPrime P) x) := by sorry
