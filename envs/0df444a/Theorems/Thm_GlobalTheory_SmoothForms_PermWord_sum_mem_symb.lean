-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_sum_mem_symb
-- name    : GlobalTheory.SmoothForms.PermWord.sum_mem_symb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:39.502834+00:00
-- url     : https://prove2.me/theorems/a92bcb2f-2a6c-4d7f-be6d-3b0caff3529a
-- title:
--   Perm Word: sum mem symb
-- statement:
--   The Perm Word construction uses the sum mem symb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L197-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L197-L202

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

theorem GlobalTheory.SmoothForms.PermWord.sum_mem_symb (E : Fin n → Fin n → A) {d : ℕ} {ι : Type} [Fintype ι] (I K : ι → Fin d → Fin n) :
    (∑ i, (List.ofFn fun a => gen n (I i a) (K i a)).prod, ∑ i, (List.ofFn fun a => E (I i a) (K i a)).prod) ∈
      symb E d := by sorry
