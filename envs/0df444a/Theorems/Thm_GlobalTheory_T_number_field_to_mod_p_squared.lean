-- Prove2me | Theorems.Thm_GlobalTheory_T_number_field_to_mod_p_squared
-- name    : GlobalTheory.T.number_field_to_mod_p_squared
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:59.334039+00:00
-- url     : https://prove2.me/theorems/60e740f0-1322-4c0a-9fcc-25d0ea0df2a0
-- title:
--   T: number field to mod p squared
-- statement:
--   The T construction uses the number field to mod p squared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/NumberFieldToModPSquared.lean#L4-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/NumberFieldToModPSquared.lean#L4-L5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NumberFieldToModPSquared
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_NumberFieldToModPSquared
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial

theorem GlobalTheory.T.number_field_to_mod_p_squared : ∀ (K : Type) [Field K] [NumberField K] (S : Finset K) (n : ℕ), ∃ p : ℕ, p.Prime ∧ n < p ∧ Nonempty (Subring.closure (S : Set K) →+* ZMod (p ^ 2)) := by sorry
