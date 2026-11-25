-- Prove2me | Theorems.Thm_GlobalTheory_sum_pairs_weight_mul_class_le_mul_sum
-- name    : GlobalTheory.sum_pairs_weight_mul_class_le_mul_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:40:41.665963+00:00
-- url     : https://prove2.me/theorems/a87387f7-cb8b-43ac-8bcc-b57ed13e7c6d
-- title:
--   Global Theory: sum pairs weight mul class le mul sum
-- statement:
--   The Global Theory construction uses the sum pairs weight mul class le mul sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumPairsWeightMulClassLeMulSum.lean#L7-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumPairsWeightMulClassLeMulSum.lean#L7-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumPairsWeightMulClassLeMulSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
open GlobalTheory

theorem GlobalTheory.sum_pairs_weight_mul_class_le_mul_sum (α β : Type) (S : Finset (α × α)) (cls : α → β)
    (w : α → ℝ) (om : β → ℝ) (T₁ T₂ : Finset β) (hw : ∀ a, 0 ≤ w a) (hom : ∀ b, 0 ≤ om b)
    (hT : ∀ p ∈ S, cls p.1 ∈ T₁ ∧ cls p.2 ∈ T₂)
    (hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → cls p.2 = cls q.2 → p = q)
    (hsum : ∀ b, ∑ a ∈ (S.image Prod.fst).filter (fun a => cls a = b), w a ≤ 1) :
    ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2)) ≤ (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by sorry
