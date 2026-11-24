-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_exists_symb
-- name    : GlobalTheory.SmoothForms.PermWord.exists_symb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:18:38.857583+00:00
-- url     : https://prove2.me/theorems/57e44334-21a9-4ba8-b2bc-008f07d47b6d
-- title:
--   Perm Word: exists symb
-- statement:
--   The Perm Word construction uses the exists symb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L217-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L217-L234

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

theorem GlobalTheory.SmoothForms.PermWord.exists_symb {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (d : ℕ)
    (π : Equiv.Perm (Fin d)) : ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)),
      (∑ K : Fin d → Fin n, (List.ofFn fun a => gen n (K (π a)) (K a)).prod, c) ∈ symb E d := by sorry
