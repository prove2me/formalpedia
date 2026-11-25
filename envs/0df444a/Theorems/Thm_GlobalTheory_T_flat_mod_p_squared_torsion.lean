-- Prove2me | Theorems.Thm_GlobalTheory_T_flat_mod_p_squared_torsion
-- name    : GlobalTheory.T.flat_mod_p_squared_torsion
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:23.09602+00:00
-- url     : https://prove2.me/theorems/69117552-21c6-41e1-9579-2729f62be810
-- title:
--   T: flat mod p squared torsion
-- statement:
--   The T construction uses the flat mod p squared torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FlatModPSquaredTorsion.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FlatModPSquaredTorsion.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlatModPSquaredTorsion
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FlatModPSquaredTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI

theorem GlobalTheory.T.flat_mod_p_squared_torsion : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by sorry
