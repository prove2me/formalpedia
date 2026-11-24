-- Prove2me | Theorems.Thm_GlobalTheory_exists_leading_minors_ge_of_le_rank
-- name    : GlobalTheory.exists_leading_minors_ge_of_le_rank
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:54.742964+00:00
-- url     : https://prove2.me/theorems/7730ed04-002a-4d29-8daf-76569c88604c
-- title:
--   Global Theory: exists leading minors ge of le rank
-- statement:
--   The Global Theory construction uses the exists leading minors ge of le rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLeadingMinorsGeOfLeRank.lean#L27-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLeadingMinorsGeOfLeRank.lean#L27-L104

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

theorem GlobalTheory.exists_leading_minors_ge_of_le_rank {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {r : ℕ} (A : Set (Fin r → O))
    {c : O} (hc : c ≠ 0) (hA : ∀ x : Fin r → O, c • x ∈ Submodule.span O A) :
    ∀ n : ℕ, n ≤ r → ∃ t : ℕ → Fin r → O, (∀ i, i < n → t i ∈ A) ∧
      ∀ (m : ℕ) (hm : m ≤ r), m ≤ n → v (algebraMap O C c) ^ m ≤
        v (algebraMap O C (Matrix.of fun a i : Fin m => t i (Fin.castLE hm a)).det) := by sorry
