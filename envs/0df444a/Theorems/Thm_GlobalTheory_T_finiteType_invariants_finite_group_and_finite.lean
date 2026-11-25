-- Prove2me | Theorems.Thm_GlobalTheory_T_finiteType_invariants_finite_group_and_finite
-- name    : GlobalTheory.T.finiteType_invariants_finite_group_and_finite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:32.051774+00:00
-- url     : https://prove2.me/theorems/638bdf69-4291-4f4d-a0cd-bc52632ea346
-- title:
--   T: finite Type invariants finite group and finite
-- statement:
--   The T construction uses the finite Type invariants finite group and finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteTypeInvariantsFiniteGroupAndFiniteStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteTypeInvariantsFiniteGroupAndFiniteStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteTypeInvariantsFiniteGroupAndFinite
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteTypeInvariantsFiniteGroupAndFiniteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finiteType_invariants_finite_group_and_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra.FiniteType R C'] (G : Type) [Group G] [Finite G] (act : G →* (C' ≃ₐ[R] C')) (C : Subalgebra R C'), (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' := by sorry
