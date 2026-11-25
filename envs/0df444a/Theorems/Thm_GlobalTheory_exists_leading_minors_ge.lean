-- Prove2me | Theorems.Thm_GlobalTheory_exists_leading_minors_ge
-- name    : GlobalTheory.exists_leading_minors_ge
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:59.763525+00:00
-- url     : https://prove2.me/theorems/062b66c0-a5d2-438a-bec8-eee0e95998e0
-- title:
--   Global Theory: exists leading minors ge
-- statement:
--   The Global Theory construction uses the exists leading minors ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLeadingMinorsGeOfLeRank.lean#L106-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLeadingMinorsGeOfLeRank.lean#L106-L116

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLeadingMinorsGeOfLeRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_leading_minors_ge :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
      v.Integers O → ∀ (r : ℕ) (A : Set (Fin r → O)) (c : O), c ≠ 0 →
      (∀ x : Fin r → O, c • x ∈ Submodule.span O A) →
      ∃ t : Fin r → Fin r → O, (∀ i, t i ∈ A) ∧ ∀ s : Fin r,
        v (algebraMap O C c) ^ (s.val + 1) ≤
          v (algebraMap O C (Matrix.of fun a i : Fin (s.val + 1) =>
            t (Fin.castLE s.isLt i) (Fin.castLE s.isLt a)).det) := by sorry
