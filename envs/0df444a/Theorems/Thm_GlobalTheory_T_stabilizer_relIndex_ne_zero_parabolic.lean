-- Prove2me | Theorems.Thm_GlobalTheory_T_stabilizer_relIndex_ne_zero_parabolic
-- name    : GlobalTheory.T.stabilizer_relIndex_ne_zero_parabolic
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:58:45.408271+00:00
-- url     : https://prove2.me/theorems/1e147e36-ff3d-4b99-a8f4-18c77067081f
-- title:
--   T: stabilizer rel Index ne zero parabolic
-- statement:
--   The T construction uses the stabilizer rel Index ne zero parabolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StabilizerRelIndexNeZeroParabolicStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StabilizerRelIndexNeZeroParabolicStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StabilizerRelIndexNeZeroParabolic
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StabilizerRelIndexNeZeroParabolicStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.stabilizer_relIndex_ne_zero_parabolic : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ TM : Subgroup M, (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ (q : M) (X : N), (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) ≠ 0 := by sorry
