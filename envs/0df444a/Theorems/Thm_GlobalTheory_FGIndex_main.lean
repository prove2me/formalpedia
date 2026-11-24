-- Prove2me | Theorems.Thm_GlobalTheory_FGIndex_main
-- name    : GlobalTheory.FGIndex.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:17:26.760021+00:00
-- url     : https://prove2.me/theorems/11479ddd-5a9a-4f9b-90ea-278a865d1289
-- title:
--   FGIndex: main
-- statement:
--   The FGIndex construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexCoprimeOfTorsion.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexCoprimeOfTorsion.lean#L42-L44

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

theorem GlobalTheory.FGIndex.main : ∀ {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ), l.Prime → A ≤ B → B.FG →
    (∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) → A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l := by sorry
