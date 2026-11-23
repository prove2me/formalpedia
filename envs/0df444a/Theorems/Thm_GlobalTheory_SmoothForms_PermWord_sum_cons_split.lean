-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_sum_cons_split
-- name    : GlobalTheory.SmoothForms.PermWord.sum_cons_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:45.385365+00:00
-- url     : https://prove2.me/theorems/1140b8c2-b8e0-41a5-9227-0204355b3f48
-- title:
--   Perm Word: sum cons split
-- statement:
--   The Perm Word construction uses the sum cons split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L14-L17

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

theorem GlobalTheory.SmoothForms.PermWord.sum_cons_split {d : ℕ} (f : (Fin (d + 1) → Fin n) → S) :
    ∑ K, f K = ∑ K : Fin d → Fin n, ∑ j : Fin n, f (Fin.cons j K) := by sorry
