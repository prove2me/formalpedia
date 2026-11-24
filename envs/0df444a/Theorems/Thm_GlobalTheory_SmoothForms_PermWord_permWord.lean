-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_permWord
-- name    : GlobalTheory.SmoothForms.PermWord.permWord
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:00.560384+00:00
-- url     : https://prove2.me/theorems/570e0ecc-e6a0-4fad-be5c-b76e596c34fa
-- title:
--   Perm Word: perm Word
-- statement:
--   The Perm Word construction uses the perm Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L236-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L236-L245

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

theorem GlobalTheory.SmoothForms.PermWord.permWord : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (d : ℕ) (π : Equiv.Perm (Fin d)), ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)), wordMap E d (permMat n d π) - c ∈ filt E d := by sorry
