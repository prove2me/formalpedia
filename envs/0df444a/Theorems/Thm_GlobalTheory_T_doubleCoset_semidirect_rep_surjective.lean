-- Prove2me | Theorems.Thm_GlobalTheory_T_doubleCoset_semidirect_rep_surjective
-- name    : GlobalTheory.T.doubleCoset_semidirect_rep_surjective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:32:37.126793+00:00
-- url     : https://prove2.me/theorems/7e5de784-7a93-427c-8d5b-faf9277a3e1a
-- title:
--   T: double Coset semidirect rep surjective
-- statement:
--   The T construction uses the double Coset semidirect rep surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSemidirectRepSurjectiveStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSemidirectRepSurjectiveStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSemidirectRepSurjective
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSemidirectRepSurjectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.doubleCoset_semidirect_rep_surjective : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P), ∃ X : N, DoubleCoset.mk TP KP (s (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) * u X) = d := by sorry
