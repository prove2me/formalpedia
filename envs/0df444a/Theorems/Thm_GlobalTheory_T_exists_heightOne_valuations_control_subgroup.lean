-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_heightOne_valuations_control_subgroup
-- name    : GlobalTheory.T.exists_heightOne_valuations_control_subgroup
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:33.972072+00:00
-- url     : https://prove2.me/theorems/0dc1902e-52b6-4488-96ae-463e74f94100
-- title:
--   T: exists height One valuations control subgroup
-- statement:
--   The T construction uses the exists height One valuations control subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHeightOneValuationsControlSubgroupStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHeightOneValuationsControlSubgroupStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHeightOneValuationsControlSubgroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHeightOneValuationsControlSubgroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_heightOne_valuations_control_subgroup : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (J : Type) [Finite J] (g : J → (FractionRing R)ˣ), ∃ (s : ℕ) (v : Fin s → ((FractionRing R)ˣ →* Multiplicative ℤ)), (∀ i (x : (FractionRing R)ˣ) (r : R), (x : FractionRing R) = algebraMap R _ r → 0 ≤ Multiplicative.toAdd (v i x)) ∧ (∀ x ∈ Subgroup.closure (Set.range g), (∀ i, 0 ≤ Multiplicative.toAdd (v i x)) → ∃ r : R, (x : FractionRing R) = algebraMap R _ r) := by sorry
