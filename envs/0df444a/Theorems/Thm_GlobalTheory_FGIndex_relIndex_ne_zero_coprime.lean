-- Prove2me | Theorems.Thm_GlobalTheory_FGIndex_relIndex_ne_zero_coprime
-- name    : GlobalTheory.FGIndex.relIndex_ne_zero_coprime
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:17:45.813711+00:00
-- url     : https://prove2.me/theorems/ca902ac4-27ea-4fca-8717-78375b97074f
-- title:
--   FGIndex: rel Index ne zero coprime
-- statement:
--   The FGIndex construction uses the rel Index ne zero coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexCoprimeOfTorsion.lean#L6-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexCoprimeOfTorsion.lean#L6-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexCoprimeOfTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.FGIndex

theorem GlobalTheory.FGIndex.relIndex_ne_zero_coprime {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ) (hl : l.Prime)
    (_hAB : A ≤ B) (hB : B.FG) (h : ∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) :
    A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l := by sorry
