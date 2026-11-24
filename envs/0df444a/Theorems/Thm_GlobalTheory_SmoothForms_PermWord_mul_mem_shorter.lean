-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_mul_mem_shorter
-- name    : GlobalTheory.SmoothForms.PermWord.mul_mem_shorter
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:18:59.750145+00:00
-- url     : https://prove2.me/theorems/92bc7be1-8f54-4f37-b096-8d055d4a9c8d
-- title:
--   Perm Word: mul mem shorter
-- statement:
--   The Perm Word construction uses the mul mem shorter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L123-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L123-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem GlobalTheory.SmoothForms.PermWord.mul_mem_shorter (E : Fin n → Fin n → A) {d : ℕ} (z : Fin n × Fin n) {x : A} (hx : x ∈ shorter E d) :
    E z.1 z.2 * x ∈ shorter E (d + 1) := by sorry
