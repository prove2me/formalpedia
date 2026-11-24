-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_perm_sum_mem
-- name    : GlobalTheory.SmoothForms.PermWord.perm_sum_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:54.221546+00:00
-- url     : https://prove2.me/theorems/3ffd3341-0a7e-4159-abf0-469654b4ba14
-- title:
--   Perm Word: perm sum mem
-- statement:
--   The Perm Word construction uses the perm sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L43-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L43-L79

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
variable {S : Type} [CommRing S] {n : ℕ}

theorem GlobalTheory.SmoothForms.PermWord.perm_sum_mem (X : Matrix (Fin n) (Fin n) S) (T : ℕ → S → Prop) (h0 : T 0 1)
    (hs : ∀ k j p, T j p → T (k + 1 + j) ((X ^ (k + 1)).trace * p)) (d : ℕ) :
    ∀ (π : Equiv.Perm (Fin d)) (m : Fin d → ℕ),
      T (∑ a, (m a + 1)) (∑ K : Fin d → Fin n, ∏ a, (X ^ (m a + 1)) (K (π a)) (K a)) := by sorry
