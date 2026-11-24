-- Prove2me | Theorems.Thm_GlobalTheory_T_relIndex_unfold_semidirect_product
-- name    : GlobalTheory.T.relIndex_unfold_semidirect_product
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:56:30.941385+00:00
-- url     : https://prove2.me/theorems/85df7441-e6d7-407a-96f1-4cd5f32ecd14
-- title:
--   T: rel Index unfold semidirect product
-- statement:
--   The T construction uses the rel Index unfold semidirect product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUnfoldSemidirectProductStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUnfoldSemidirectProductStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUnfoldSemidirectProduct
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUnfoldSemidirectProductStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.relIndex_unfold_semidirect_product : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), (TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom).relIndex CP = (TM ⊓ KM.map (MulAut.conj q).toMonoidHom).relIndex CM * (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by sorry
