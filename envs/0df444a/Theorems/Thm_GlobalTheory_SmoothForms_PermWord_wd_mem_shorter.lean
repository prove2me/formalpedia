-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_mem_shorter
-- name    : GlobalTheory.SmoothForms.PermWord.wd_mem_shorter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:44.204663+00:00
-- url     : https://prove2.me/theorems/0ee5d18a-e383-4490-9841-235739f10141
-- title:
--   Perm Word: wd mem shorter
-- statement:
--   The Perm Word construction uses the wd mem shorter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L102-L103

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

theorem GlobalTheory.SmoothForms.PermWord.wd_mem_shorter (E : Fin n → Fin n → A) {d : ℕ} {l : List (Fin n × Fin n)} (h : l.length < d) :
    wd E l ∈ shorter E d := by sorry
