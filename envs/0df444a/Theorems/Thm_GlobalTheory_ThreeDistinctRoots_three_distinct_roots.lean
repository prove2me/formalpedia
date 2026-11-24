-- Prove2me | Theorems.Thm_GlobalTheory_ThreeDistinctRoots_three_distinct_roots
-- name    : GlobalTheory.ThreeDistinctRoots.three_distinct_roots
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:07:41.186281+00:00
-- url     : https://prove2.me/theorems/abcb488d-ab41-412b-9f1f-bfb5af617147
-- title:
--   Three Distinct Roots: three distinct roots
-- statement:
--   The Three Distinct Roots construction uses the three distinct roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ThreeDistinctRoots.lean#L7-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ThreeDistinctRoots.lean#L7-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ThreeDistinctRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ThreeDistinctRoots
open Polynomial

theorem GlobalTheory.ThreeDistinctRoots.three_distinct_roots :
    ∀ {K : Type} [inst : Field K] [IsAlgClosed K] (g₂ g₃ : K), (2 : K) ≠ (0 : K) →
      g₂ ^ (3 : ℕ) - (27 : K) * g₃ ^ (2 : ℕ) ≠ (0 : K) →
      ∃ (x : K) (y : K) (z : K), x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        (4 : K) * x ^ (3 : ℕ) - g₂ * x - g₃ = (0 : K) ∧
        (4 : K) * y ^ (3 : ℕ) - g₂ * y - g₃ = (0 : K) ∧
        (4 : K) * z ^ (3 : ℕ) - g₂ * z - g₃ = (0 : K) := by sorry
