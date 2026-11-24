-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_symb_sub
-- name    : GlobalTheory.SmoothForms.PermWord.symb_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:02.992823+00:00
-- url     : https://prove2.me/theorems/62f1ea02-7b9a-4240-8366-5800642d2b5e
-- title:
--   Perm Word: symb sub
-- statement:
--   The Perm Word construction uses the symb sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L182-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L182-L195

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

theorem GlobalTheory.SmoothForms.PermWord.symb_sub {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) {d : ℕ} {x} (hx : x ∈ symb E d) :
    x.2 - order E x.1 ∈ shorter E d := by sorry
