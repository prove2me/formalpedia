-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_int_span_generators_of_isLattice_pi
-- name    : GlobalTheory.T.exists_int_span_generators_of_isLattice_pi
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:44.580852+00:00
-- url     : https://prove2.me/theorems/229d376b-80a2-4f39-944d-487ea3ce9ec6
-- title:
--   T: exists int span generators of is Lattice pi
-- statement:
--   The T construction uses the exists int span generators of is Lattice pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIntGeneratorsCardEqOfIsLatticePiStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIntGeneratorsCardEqOfIsLatticePiStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntGeneratorsCardEqOfIsLatticePi
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntGeneratorsCardEqOfIsLatticePiStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_int_span_generators_of_isLattice_pi : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E Λ → ∃ u : Fin (Module.finrank ℚ E * n) → Fin n → E, (∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range u)) ∧ Submodule.span ℚ (Set.range u) = ⊤ := by sorry
