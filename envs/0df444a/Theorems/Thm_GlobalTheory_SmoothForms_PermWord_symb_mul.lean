-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_symb_mul
-- name    : GlobalTheory.SmoothForms.PermWord.symb_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:37.460893+00:00
-- url     : https://prove2.me/theorems/d3aeb47e-a8a3-43fe-9f51-7d1c15486a96
-- title:
--   Perm Word: symb mul
-- statement:
--   The Perm Word construction uses the symb mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L174-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L174-L180

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

theorem GlobalTheory.SmoothForms.PermWord.symb_mul (E : Fin n → Fin n → A) {a b : ℕ} {x y} (hx : x ∈ symb E a) (hy : y ∈ symb E b) :
    x * y ∈ symb E (a + b) := by sorry
