-- Prove2me | Theorems.Thm_GlobalTheory_NearlyPrimitive_exists_last_max
-- name    : GlobalTheory.NearlyPrimitive.exists_last_max
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:04.554519+00:00
-- url     : https://prove2.me/theorems/16c41991-6f67-4033-810c-156b3d479b94
-- title:
--   Nearly Primitive: exists last max
-- statement:
--   The Nearly Primitive construction uses the exists last max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L98-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L98-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology

theorem GlobalTheory.NearlyPrimitive.exists_last_max (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (n : ℕ) (hn : 1 < t n) :
    ∃ k, 1 < t k ∧ (∀ a, t a ≤ t k) ∧ ∀ a, k < a → t a < t k := by sorry
